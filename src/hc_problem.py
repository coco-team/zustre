###
### A representation of Linear Horn Clause SAT problem
###

import z3
import z3_utils as z3u
import hcp_utils
import dfs
import stats


def mk_pre_const (pred, arg): return _mk_arg_const (pred, arg, 0)
def mk_post_const (pred, arg): return _mk_arg_const (pred, arg, 1)

def _mk_arg_const (pred, arg, variant=0):
  """
  Returns a constant representing variant 'variant' argument 'arg' of
  predicate 'pred'
  """

  if not isinstance (pred, z3.FuncDeclRef) : pred = pred.decl ()

  name = "{}_{}_{}".format (pred.name (), arg, variant)
  return z3.Const (name, pred.domain (arg))

def _mk_const_variant (c, variant):
  return z3.Const (c.decl ().name () + '_' + str (variant),
                   c.sort ())
  
def _mk_pre_lemma (pred, lemma): return _mk_variant_lemma (pred, lemma, 0)
def _mk_post_lemma (pred, lemma): return _mk_variant_lemma (pred, lemma, 1)

@stats.time_stats
def _mk_variant_lemma (pred, lemma, variant=0):
  """
  Converts a lemma over a predicate to be over a given set of
  variables of that predicate
  """
  if pred is None: return lemma
  if not isinstance (pred, z3.FuncDeclRef) : pred = pred.decl ()

  args = [_mk_arg_const (pred, i, variant) for i in range (pred.arity ())]
  rw = z3u.SubstituteVars (*args)
  return rw (lemma)

def mk_post_lemma_variant (pred, lemma, variant):
  return _mk_variant_lemma (pred, lemma, variant=variant+1)

def ground_rule (rule_exp):
  """ Strip quantifier and replace bound vars by constants"""
  aux, matrix = z3u.stripQuantifierBlock (rule_exp)

  if z3u.isZ3Implies (matrix):
    body = matrix.arg (0)
    head = matrix.arg (1)
  else:
    head = matrix
    body = z3u.mk_true (rule_exp.ctx)

  return (aux, head, body)


def split_body (body):
  """ Splits body into Pred and Tail, where Pred is the only
  uninterpreted predicate (instance), and tail is all interpreted"""
  pred = z3u.getFirstConjunct (body)
  if pred.decl ().kind () != z3.Z3_OP_UNINTERPRETED:
    pred = None
    tail = body.children ()
  else:
    assert body.num_args () > 0
    tail = []
    if z3.is_and (body):
      tail.extend (body.children ()[1:])
  return pred, tail

def elim_pred (pred, variant=0) :
  if pred == None : return []
  pred_decl = pred.decl ()
  eqs = []
  for i in range (pred.num_args ()):
    const = _mk_arg_const (pred_decl, i, variant)
    arg = pred.arg (i)
    if not arg.eq (const):  eqs.append (arg == const)
  return eqs

def elim_pre_pred (pred): return elim_pred (pred, variant=0)
def elim_post_pred (pred): return elim_pred (pred, variant=1)

def elim_preds (head, pred, tail):
  res = []
  if pred != None:
    res = elim_pre_pred (pred)
    pred_decl = pred.decl ()
  else:
    pred_decl = None

  if head != None:
    res.extend (elim_post_pred (head))
    head_decl = head.decl ()
  else:
    head_decl = None
   
  return head_decl, pred_decl, res

def mk_pre_pred_consts (pdecl): return mk_pred_consts (pdecl, variant=0)
def mk_post_pred_consts (pdecl): return mk_pred_consts (pdecl, variant=1)

def mk_pred_consts (pdecl, variant=0) :
  return [_mk_arg_const (pdecl, i, variant) for i in range (pdecl.arity ())]

class Rule (z3u.HelperBase):
  def __init__ (self, rule_exp):
    z3u.HelperBase.__init__ (self, rule_exp.ctx)
    self.origin = rule_exp
    self.tag = None

    # parent pt 
    self.parent = None

    self._init_from_rule_expr (rule_exp)
    self._exists_aux = z3u.MkExists (self.aux)
    self.qvars = None
    assert self.head.kind () == z3.Z3_OP_UNINTERPRETED
    assert self.src is None or \
        self.src.kind () == z3.Z3_OP_UNINTERPRETED

    
  def _init_from_rule_expr (self, rule_exp):
    """" Make first-order transition relation for the rule_exp """
    aux, head, body = ground_rule (rule_exp)
    pred, tail = split_body (body)

    hdecl, pdecl, state_eq =  elim_preds (head, pred, tail)

    # auxiliary variables
    self.aux = aux
    # the head predicate
    self.head = hdecl
    # the src predicate
    self.src = pdecl
    # the tail of the rule
    self.tail = tail
    # equalities connecting state-variables with auxiliary variables
    self.state_eq = state_eq

  def get_src_pt (self):
    if self.src is None: return None
    return self.get_problem ().get_pt (self.src)
  def get_head_pt (self):
    return self.parent

  def get_qvars (self):
    """vars to quantify"""
    if self.qvars is None:
      # include aux
      self.qvars = self.aux [:]
      # include pre consts for src
      if self.src is not None:
        src_pt = self.get_problem ().get_pt (self.src)
        self.qvars.extend (src_pt.pre_consts ())
      # include post consts for head
      self.qvars.extend (self.parent.post_consts ())
    return self.qvars

  def set_parent (self, p): self.parent = p
  def get_parent (self): return self.parent
  def get_problem (self): return self.parent.get_parent ()
  

  def get_src (self): return self.src
  def get_head (self): return self.head
  def get_origin (self): return self.origin

  def get_tag (self):
    if self.tag is not None : return self.tag
    if self.src is None : src_name = 'none'
    else : src_name = self.src.name ()
    self.tag = z3.Const ('{}_{}_tag'.format (src_name,
                                             self.head.name ()),
                         z3.BoolSort (ctx=self.ctx))
    return self.tag

  def mk_rule (self):
    body = []
    if self.src is not None:
      src_pt = self.get_problem ().get_pt (self.src)
      body.append (src_pt.pre_inst ())
    body.extend (self.tail)
    body.extend (self.state_eq)

    matrix = self.parent.post_inst ()

    and_body = self.mk_and (*body)
    if not z3.is_true (and_body):
      matrix = z3.Implies (and_body, matrix)

    qvars = self.get_qvars ()

    return z3u.z3ForAll (qvars, matrix)

  def box (self, *args, **kwrds): return self.mk_rule ()


  def __repr__ (self) :
    return self.mk_rule ().sexpr ()


class PredTransformer (z3u.HelperBase):
    def __init__ (self, pred):
        z3u.HelperBase.__init__ (self, pred.ctx)
        # unique id of the transformer 
        self.id = None
        # the head predicate (z3.FuncDeclRef)
        self.head = pred
        # rules defining the transformer
        self.rules = list ()

        ### AG: I don't think this is needed any more.
        ### AG: instead, store in each PT a pointer to the HC problem 
        ### AG: it is from (say under self.hcp). Then, to get the src for 
        ### AG: the rule do  self.hcp.get_pt (rule.srcPred ())
        ### AK: we can, but does it hurt? as we have users (below), we can have
        ###      this as well
        # src pts of the rules
        self.srcs = list ()

        # predicate transformers that use `self' in some body
        self.users = list ()

        # original transformer we came from
        self.origin = None


        self.tag = None
        self.tag2 = None
        self.pre_cond = None
        self.trans = None
        self.bg = None

        # invariants for pt
        self.invs = z3.AstVector (ctx=self.ctx)

        self.parent = None

        self._pre_consts = [_mk_arg_const (self.head, i, 0) 
                            for i in range (self.head.arity ())]
        self._post_consts = [_mk_arg_const (self.head, i, 1) 
                             for i in range (self.head.arity ())]
        self._pre_inst = self.head (*self._pre_consts)
        self._post_inst = self.head (*self._post_consts)

        self.pre_rewriter = z3u.SubstituteVars (*self._pre_consts)
        self.post_rewriter = z3u.SubstituteVars (*self._post_consts)

    def mk_pre_lemma (self, lemma):
      return self.pre_rewriter (lemma)
    def mk_post_lemma (self, lemma):
      return self.post_rewriter (lemma)

    def mk_pre_invs (self) :
      was_at_pt = self.get_pre_cond ()
      pre_invs = [z3.Implies (was_at_pt,
                              self.mk_pre_lemma (inv))
                  for inv in self.get_invs ()]
      return pre_invs

    def mk_pre_inv (self, inv):
      return z3.Implies (self.get_pre_cond (), self.mk_pre_lemma (inv))

    def mk_tagged_post_invs (self):
      post_invs = [z3.Implies (self.get_tag (),
                               self.mk_post_lemma (inv))
                   for inv in self.get_invs ()]
      return post_invs

    def mk_tagged_post_inv (self, inv):
      return z3.Implies (self.get_tag (), self.mk_post_lemma (inv))

    def mk_post_invs (self):
      post_invs = [self.mk_post_lemma (inv)
                   for inv in self.get_invs ()]
      return post_invs

    def pre_const (self, i):
      return self._pre_consts [i]
    def post_const (self, i):
      return self._post_consts [i]

    def pre_consts (self): return self._pre_consts
    def post_consts (self): return self._post_consts

    def pre_inst (self): return self._pre_inst
    def post_inst (self): return self._post_inst

    
    def populate_fp (self, fp, bval=None, use_invs=False, strengthen_trans=False):
      """ Adds rules to fp """
      ### box up the rules and add to fp
      assert self.ctx == fp.ctx

      for r in self.rules:
        fp.add_rule (r.box ())

      ### add invs
      if use_invs:
        for inv in self.invs: fp.add_cover (-1, self.head, inv)

    def set_id (self, id) : self.id = id
    def get_id (self) : return self.id
    def set_parent (self, p): self.parent = p
    def get_parent (self): return self.parent

    def get_head (self): return self.head
    
    def add_user (self, pt):
        assert pt not in self.users
        self.users.append (pt)

    def add_src (self, pt) :
        assert pt not in self.srcs
        self.srcs.append (pt)

    def add_rule (self, rule) : 
      self.rules.append (rule)
      rule.set_parent (self)

    def get_rules (self): return self.rules
    def get_num_rules (self): return len (self.rules)

    def get_rule_from (self, pt) :
      if pt not in self.srcs : return None
      return self.rules [self.srcs.index (pt)]

    def user_rules (self):
      """generator for rules using self"""
      for user in self.users :
        r = user.get_rule_from (self)
        if r is not None : yield r

    def is_behind (self, u): return self.id <= u.id

    def set_origin_pt (self, pt) : self.origin = pt

    def get_tag (self):
      if self.tag is not None : return self.tag
      self.tag = z3.Const ('{}_tag'.format (self.head.name ()),
                           z3.BoolSort (ctx=self.ctx))
      return self.tag
    
    def get_tag2 (self):
      if self.tag2 is not None : return self.tag2
      self.tag2 = z3.Const ('{}_tag!2'.format (self.head.name ()),
                           z3.BoolSort (ctx=self.ctx))
      return self.tag2


    def get_pre_cond (self):
      """return constraint for being at self in the previous time step
      """
      if self.pre_cond is not None: return self.pre_cond
      out_tags = [r.get_tag () for r in self.user_rules ()]
      self.pre_cond = self.mk_or (*out_tags)
      return self.pre_cond

    def is_concrete (self):
      return True


    def add_inv (self, inv, add_to_solver=True):
      if inv not in self.invs:
        self.invs.push (inv)
        if add_to_solver:
          self.parent.add_to_solver (self.mk_pre_inv (inv))
          self.parent.add_to_solver (self.mk_tagged_post_inv (inv))

    def is_inv (self, lem):
      return (lem in self.invs)

    def get_invs (self) : return self.invs

    def __repr__ (self): return repr (self.head)
    def __repr_verbose__ (self) :
        s = ''
        for rule in self.rules : s = s + repr (rule) + '\n'
        return s
    
    # graph.Node interface
    def get_succs (self): return iter (self.users)
    def has_succ (self, n): return n in self.users


class HornClauseProblem (object):
    def __init__ (self, ctx=None):
      
      self.ctx = ctx
      if self.ctx == None: self.ctx = z3.main_ctx ()
      
      # predicate transformers
      self.pts = list ()
      # map from preds to pts
      self.ptMap = dict ()
      # special predicate transformers
      self.root = None
      self.query = None
      # true when closed
      self.closed = False
      # heterogeneous list of lists and pts
      self.wto = None

      self.trans = None

      self.solver = None

    def _createWto (self) :
      def visit (pt, curr_list, id) :
        pt.set_id (id)
        curr_list.append (pt)
        return {'id' : id + 1}

      def backedge (from_pt, pt, wto, curr_list) :
        l = wto
        while (pt not in l) : l = l[-1]
        idx = l.index (pt)
        # if pt is already a head, do nothing
        if idx == 0 : return None
        # the suffix from idx forms a new list
        new_list = l [idx:]
        # replace the suffix from idx with the new list
        l [idx:] = list ()
        l.append (new_list)
        if curr_list == l :
          curr_list = new_list
        return {'curr_list' : curr_list}

      # empty list
      self.wto = list ()

      traversal = dfs.DFS (lambda n : z3u.z3AstRefKey (n.head), lambda n : n.users)
      traversal.addHandler (visit, ['curr_list', 'id'], 'visit')
      traversal.addHandler (backedge, ['wto', 'curr_list'], 'backedge')
      traversal.setInitValue ('curr_list', self.wto)
      traversal.setInitValue ('wto', self.wto)
      traversal.setInitValue ('id', 0)
      traversal.search (self.root)

      # move query to the end of wto
      for wto_comps, pt in hcp_utils.wtoWalk (self.wto) :
        if pt == self.query :
          assert pt in wto_comps [-1]
          wto_comps [-1].remove (pt)
          break
      self.wto.append (self.query)

    def close (self):
        if self.closed : return
        assert self.root is not None
        assert self.query is not None

        # create wto numbering all pts
        if self.wto is None :
          self._createWto ()

        # mark the problem closed
        self.closed = True

    def add_pt (self, pt):
        self.pts.append (pt)
        self.ptMap [z3u.z3AstRefKey (pt.head)] = pt
        pt.set_parent (self)

    def add_rule (self, rule):
      """ adds a rule """
      ## add rule to PT that owns it
      head_pt = self.get_pt (rule.get_head ())
      assert head_pt is not None
      head_pt.add_rule (rule)

      ## update srcPT if it exists
      src_pred = rule.get_src ()
      if src_pred is None : src_pt = None
      else : src_pt = self.get_pt (src_pred)
      if src_pt is not None :
        head_pt.add_src (src_pt)
        src_pt.add_user (head_pt)
      else: head_pt.add_src (None)

    def ensure_pt (self, pred) :
        key = z3u.z3AstRefKey (pred)
        if key in self.ptMap : return self.ptMap [key]
        pt = PredTransformer (pred)
        self.add_pt (pt)
        return pt

    def get_pt (self, pred) :
        key = z3u.z3AstRefKey (pred)
        return self.ptMap.get (key)

    def set_root (self, pt):
        assert self.root is None
        self.root = pt

    def get_root (self): return self.root
    def get_query (self): return self.query

    def get_query_pred (self): return self.query.head ()

    def set_query (self, pt):
        assert self.query is None
        self.query = pt

    def is_concrete (self):
      return True

    def __repr__ (self) :
        s = 'Root : {}\n'.format (repr (self.root.head))
        for pt in self.pts : s = s + pt.__repr_verbose__ ()
        s = s + 'Query : {}\n'.format (repr (self.query.head))
        return s

    # graph.DirectedGraph interface
    def get_nodes (self): return iter (self.pts)


def hc_from_fp (fp, query):
  """ Create a HornClauseProblem from z3.FixedPoint object """
  p = HornClauseProblem (fp.ctx)
  rules = list ()

  # create pts
  for rule_exp in fp.get_rules () :
    rule = Rule (rule_exp)
    head_pred = rule.get_head ()
    pt = p.ensure_pt (head_pred)
    if rule.get_src () is None: p.set_root (pt)
    rules.append (rule)

  # add rules to prob
  for rule in rules : p.add_rule (rule)

  # only one query for now
  assert len(query) == 1
  pt = p.get_pt (query[0].decl ())
  assert pt is not None
  p.set_query (pt)

  p.close ()
  return p

@stats.time_stats
def create_hc_problem (filename, pp=False, z3ctx=None, dummy_query=False) :
  fp = z3.Fixedpoint (ctx=z3ctx)
  if not pp:
    print 'No pre-processing'
    fp.set (slice=False)
    fp.set (inline_linear=False)
    fp.set (inline_eager=False)

  with stats.timer ('fp.parse_file'):
    q = fp.parse_file (filename)
  
  if dummy_query:
    with stats.timer ('fp.dummy_query'):
      fp.query (z3u.mk_true (z3ctx))


  prob = HornClauseProblem (z3ctx)

  rules = list ()

  # create pts
  for rule_exp in fp.get_rules () :
    rule = Rule (rule_exp)
    head_pred = rule.get_head ()
    pt = prob.ensure_pt (head_pred)
    if rule.get_src () is None: prob.set_root (pt)
    rules.append (rule)

  # add rules to prob
  for rule in rules : prob.add_rule (rule)

  # only one query for now
  assert len(q) == 1
  pt = prob.get_pt (q[0].decl ())
  assert pt is not None
  prob.set_query (pt)


  del fp
  return prob

if __name__ == '__main__':
  import sys
  p = create_hc_problem (sys.argv[1])
  p.close ()
  
  print '======================================================================'
  for pt in p.pts:
    for r in pt.get_rules ():
      if r.src is None: continue
      print r.get_tag (), '-> BODY'
      print r.get_tag (), '->', r.get_src_pt ().get_tag ()
  print '----------------------------------------------------------------------'
  for pt in p.pts:
    if pt == p.get_root () : continue
    pred_tags = [r.get_tag () for r in pt.get_rules ()]
    print pt.get_tag2 (), '-> OR(', pred_tags, ')'
    

      # if r.src is not None:
      #   print  r.get_src_pt ().pre_inst (), '->', r.get_head_pt ().post_inst ()

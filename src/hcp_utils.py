##
## Utility methods 
##

import z3
import z3_utils as z3u

import stats

def wtoTopo (order) :
  for elem in order :
    if isinstance (elem, list) :
      for pt in wtoTopo (elem) :
        yield pt
    else :
      yield elem

def wtoWalk (order, wto_comps=[]) :
  init_size = len (wto_comps)
  for elem in order :
    if isinstance (elem, list) :
      wto_comps.append (elem)
      for comps,pt in wtoWalk (elem, wto_comps) :
        try :
          yield (comps, pt)
        except GeneratorExit :
          if len (wto_comps) > init_size :
            del wto_comps [init_size:]
          return
      wto_comps.pop ()
    else :
      try :
        yield (wto_comps, elem)
      except GeneratorExit :
        if len (wto_comps) > init_size :
          del wto_comps [init_size:]
        return

def userRulesWalk (pt) :
  """generator for the rules which use pt ; assume that any pt' uses pt
in at most one rule
  """
  for user in pt.users :
    try:
      yield (user, user.rules [user.srcs.index (pt)])
    except ValueError:
      pass

def srcRulesWalk (pt) :
  """generator for the rules defining pt
  """
  assert len (pt.srcs) == len (pt.rules)
  for i in range (len (pt.rules)) :
    yield (pt.srcs [i], pt.rules [i])

def is_back_edge (fro, to) :
  return (fro is not None) and (to.is_behind (fro))

def isInWtoComponent (pt, comp) :
  for _pt in wtoTopo (comp) :
    if _pt == pt : return True
  return False

def walk_cex_trace (trace, top_down=True):
  """generator for pairs of pred. instances corresponding to steps of the trace

  trace is a z3 and expression - And (query!<x>, L1(..), L2(..), ...)
  """
  assert z3.is_and (trace)
  n = trace.num_args ()
  if n <= 2 : return
  if top_down :
    curr_pred = None
    for i in range (n-1, 0, -1):
      next_pred = trace.arg (i)
      yield (curr_pred, next_pred)
      curr_pred = next_pred
  else :
    next_pred = trace.arg (1)
    for i in range (2, n, 1):
      curr_pred = trace.arg (i)
      yield (curr_pred, next_pred)
      next_pred = curr_pred
    yield (None, next_pred)

def MUS_elim_sat (solver, true_lits, free_vars):
  """return a minimal subset of free_vars to be made true for the assertions
in solver to be unsat; proceeds by repeatedly eliminating free vars in a sat
assignment 

  assume : making all free_vars true makes the assertions in solver unsat
  assume : true_lits, free_vars and return value are all z3.AstVector objects

  as the solver need not return a min. sat assignment, the returned subset
need not be the 'minimum'
  """
  assert solver is not None
  assert isinstance (true_lits, z3.AstVector)
  assert isinstance (free_vars, z3.AstVector)

  assumptions = z3.AstVector (ctx=true_lits.ctx)
  # initialize with true_lits
  z3u.extend (assumptions, true_lits)
  to_ret = z3.AstVector (ctx=free_vars.ctx)

  curr_free_vars = free_vars
  while True:
    res = solver.check (*assumptions)
    if len (to_ret) == len (free_vars) :
      assert res == z3.unsat
      break
    if res == z3.sat:
      m = solver.model ()
      count = 0
      new_free_vars = z3.AstVector (ctx=free_vars.ctx)
      for fv in curr_free_vars :
        if z3.is_false (m.get_interp (fv)):
          to_ret.push (fv)
          assumptions.push (fv)
          count += 1
        else: new_free_vars.push (fv)
      curr_free_vars = new_free_vars
      assert count > 0
    elif res == z3.unsat : break
  return to_ret

def min_unsat_subset (solver, true_lits, free_vars) :
  """return a minimal subset of free_vars to be made true for the assertions
in solver to be unsat

  as the solver need not return a min. sat assignment, the returned subset
need not be the 'minimum'
  """
  return MUS_elim_sat (solver, true_lits, free_vars)


class AssumedLemmas (object) :
  def __init__ (self, assump_maker, ctx=None) :
    self.assump_maker = assump_maker
    self.ctx = ctx
    # maps from assumptions to (pt, lemma) pairs and viceversa
    self.atol = z3.AstMap (ctx=self.ctx)
    self.ltoa = z3.AstMap (ctx=self.ctx)

  def assume (self, l) :
    assert l not in self.ltoa
    a = self.assump_maker ()
    self.atol [a] = l
    self.ltoa [l] = a
    return a

  def get_lemma (self, a) :
    if a in self.atol: return self.atol [a]
    else : return None

  def get_assump (self, l) :
    if l in self.ltoa: return self.ltoa [l]
    else: return None

  def has_assump (self, a): return a in self.atol

  def get_assumps (self) : return self.atol.keys ()

def sprinkle_assumptions (f, assumed_lemmas):
  
  a = assumed_lemmas.get_assump (f)
  if a is not None: return z3.Implies (a, f)
  
  if z3.is_and (f) or z3.is_or (f):
    
    kids = [sprinkle_assumptions (k, assumed_lemmas) for k in f.children ()]
    if z3.is_and (f): return z3.And (*kids)
    if z3.is_or (f): return z3.Or (*kids)
  elif z3.is_true (f) or z3.is_false (f): return f
  else:
    return z3.Implies (assumed_lemmas.assume (f), f)
  
  
@stats.time_stats
def mus_ltf (s, *a):
  """ MUS loop-till-fix """
  core = None

  print 'MUS', len(a)

  with z3u.pushed_solver (s):
    res = s.check (*a)
    if res == z3.unsat:
      core = s.unsat_core ()
      if len (core) == len(a) or len (core) == 0:
        return z3.unsat, core
    else:
      return res, None
    
  return mus_ltf (s, *core)
  

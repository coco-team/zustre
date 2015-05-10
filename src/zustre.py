#!/usr/bin/env python

import z3
import z3core
import stats

from z3_utils import *
from LogManager import LoggingManager
import os,subprocess,sys
import shutil
from CoCoSpec import CoCoSpec
import stats
from kind2 import Kind2

root = os.path.dirname (os.path.dirname (os.path.realpath (__file__)))
verbose=False
xml=False

class Zustre(object):
    def __init__(self, args, ctx, fp):
        self.log = LoggingManager.get_logger(__name__)
        self.args = args
        self.fp = fp
        self.ctx = ctx
        self.coco = CoCoSpec(self.args)
        if self.args.xml: LoggingManager.disable_logger()
        return



    def isexec (self, fpath):
        if fpath == None: return False
        return os.path.isfile(fpath) and os.access(fpath, os.X_OK)

    def which(self,program):
        fpath, fname = os.path.split(program)
        if fpath:
            if isexec (program):
                return program
        else:
            for path in os.environ["PATH"].split(os.pathsep):
                exe_file = os.path.join(path, program)
                if isexec (exe_file):
                    return exe_file
        return None

    def getLustreC (self):
        lustrec = None
        if 'LUSTREC' in os.environ:
            lustrec = os.environ ['LUSTREC']
        if not self.isexec (lustrec):
            lustrec = os.path.join (root, "bin/lustrec")
        if not self.isexec (lustrec):
            raise IOError ("Cannot find LustreC")
        return lustrec


    def getKind2 (self):
        kind2 = None
        if 'KIND2' in os.environ:
            kind2 = os.environ ['KIND2']
        if not self.isexec (kind2):
            lustrec = os.path.join (root, "bin/kind2")
        if not self.isexec (kind2):
            raise IOError ("Cannot find KIND2")
        return kind2


    def mkHorn(self):
        lusFile = self.args.file
        self.log.info("Modular Hornification ... " + str(lusFile))
        hornDefs = None
        with stats.timer('Lustre2Horn'):
            top_node = 'top' if not self.args.node else self.args.node #TODO : check directly which node is top

            lusFile_dir = os.path.dirname(os.path.abspath(lusFile)) + os.sep
            lustrec = self.getLustreC();
            opt_traces = ["-horn-traces"] if self.args.cg else []
            cmd = [lustrec, "-horn", "-node", top_node, "-horn-query"] + opt_traces + ["-d", lusFile_dir, lusFile]
            p = subprocess.Popen(cmd, shell=False, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            hornDefs, _ = p.communicate()
            if "done" in hornDefs:
                base = (os.path.splitext(os.path.basename(lusFile)))[0]
                smt2_file = lusFile_dir + base + ".smt2"
                #parse trace file
                tracefile = lusFile_dir + base + ".traces.xml"
                self.coco.set_ctx(self.ctx)
                if self.args.cg: self.coco.parseTraceFile(tracefile)
                #z3printer.getCoCo(coco.varMapping)
                return smt2_file
            else:
                self.log.error(hornDefs)
                return None


    def mk_contract (self, preds):
        lusFile = self.args.file
        self.log.info("Building CoCoSpec ...")
        #s = z3.Solver(ctx=fp.ctx) # to build an SMT formula
        for p in preds:
            # create an app by creating dummy variables using p.arity () and p.domain()
            lemmas = fp_get_cover_delta (self.fp, p)
            self.coco.addContract(p.decl(),lemmas)
        cocoFile_dir = os.path.dirname(os.path.abspath(lusFile)) + os.sep
        cocoFileName = cocoFile_dir + os.path.basename(lusFile) + ".coco"
        cocoSpec = self.coco.mkCoCoSpec(lusFile)
        with open(cocoFileName,"w") as f:
            f.write(cocoSpec)
            self.log.info("Contract Generated in: %s", str(cocoFileName))
        if self.args.kind2:
            kind2 = Kind2(self.args)
            try:
                kind2.validate(cocoFileName)
            except Exception as e:
                self.log.exception(str(e))


    def mk_cex(self):
        self.log.info("Constructing the cex")
        #1. get_rules_along_trace: gives the bottom-up sequence of rules along the trace
        #2. get_ground_sat_answer: gives a bottom-up ground cex along the trace -- it's a sequence of instantiations of the form "P(0,1,0,0)", etc.
        self.log.warning("Work in progress printing CEX")
        print self.fp.get_rules_along_trace()
        print self.fp.get_ground_sat_answer()


    def encodeAndSolve(self):
        #Generate horn formulas and solve
        self.fp.set (engine='spacer')
        if self.args.stat:
            self.fp.set('print.statistics',True)
        self.fp.set('use_heavy_mev',True)
        self.fp.set('pdr.flexible_trace',True)
        self.fp.set('reset_obligation_queue',False)
        self.fp.set('spacer.elim_aux',False)
        if self.args.utvpi: self.fp.set('pdr.utvpi', False)
        if not self.args.pp:
            self.log.info("No pre-processing")
            self.fp.set ('xform.slice', False)
            self.fp.set ('xform.inline_linear',False)
            self.fp.set ('xform.inline_eager',False)

        hornFormulas = self.args.file if self.args.smt2 else self.mkHorn()
        if not hornFormulas:
            self.log.error('Problem generating Horn formulae')
            assert False
        with stats.timer ('Parse'):
            self.log.info('Successful Horn VCC generation ... ' + str(hornFormulas))
            q = self.fp.parse_file (hornFormulas)
        preds = fp_get_preds(self.fp) # get the predicates before z3 starts playing with them
        if self.args.invs :
            lemmas = z3.parse_smt2_file (args.invs, sorts={}, decls={}, ctx=ctx)
            if z3.is_and (lemmas):
                lemmas = lemmas.children ()
            for l in lemmas:
                if verbose: print l
                fp_add_cover (self.fp, l.arg(0), l.arg(1))
        with stats.timer ('Query'):
            res = self.fp.query (q[0])
            if res == z3.sat:
                stat ('Result', 'CEX')
                if self.args.xml:
                    stats.xml_print()
                else:
                    print '------- CEX ------ '
                    print self.mk_cex()
                    print '------------------ '
            elif res == z3.unsat:
                stat ('Result', 'SAFE')
                if self.args.xml: stats.xml_print()
                if self.args.cg: self.mk_contract (preds)


    def encode(self):
        # generate horn do not solve
        hornFormulas = mkHorn()
        if not hornFormulas:
            self.log.error('Problem generating Horn formulae')
            stat ('Result', 'ERR')
        else:
            stat ('Result', 'SUCCESS')
        return hornFormulas



def fp_add_cover (fp, pred, lemma, level=-1):
    # no trivial lemmas
    if z3.is_true (lemma): return

    assert (z3.is_app (pred))
    sub = []
    for i in range (0, pred.num_args ()):
        arg = pred.arg (i)
        sub.append ((arg,
                     z3.Var (i, arg.decl ().range ())))

    tlemma = z3.substitute (lemma, sub)
    if verbose:
        print "Lemma for ", pred.decl (), ": ", tlemma
    fp.add_cover (level, pred.decl (), tlemma)


def fp_get_cover_delta (fp, pred, level=-1):
    sub = []
    for i in range (0, pred.num_args ()):
        sub.append (pred.arg (i))
    lemma = fp.get_cover_delta (level, pred.decl ())
    if z3core.Z3_get_bool_value (fp.ctx.ctx, lemma.as_ast ()) != z3.unsat:
        lemma = z3.substitute_vars (lemma, *sub)
    return lemma


def fp_get_predicates (fp):
    return find_atomic_terms \
        (mk_nary (z3.And, mk_true (fp.ctx),
                      fp.get_rules ()))

def fp_get_preds (fp):
    seen = set ()
    res = list ()
    for rule in fp.get_rules ():
        pred = rule
        # A rule is of the form
        # FORALL? (BODY IMPLIES)? PRED
        if z3.is_quantifier (pred): pred = pred.body ()
        if is_implies (pred): pred = pred.arg (1)

        decl = pred.decl ()
        assert is_uninterpreted (decl)
        if z3key (decl) in seen: continue
        seen.add (z3key (decl))

        # if the rule contains a universal quantifier, replace
        # variables by properly named constants
        if z3.is_quantifier (rule):
            sub = [ z3.Const (bound_var_name (rule, i),
                              bound_var_sort (rule, i))
                    for i in range (0, rule.num_vars ()) ]
            pred = substitute_vars (pred, *sub)
        res.append (pred)
    return res



def parseArgs (argv):
    import argparse as a
    p = a.ArgumentParser (description='Zustre: A verification and contract generation engine for Lustre Programs')

    p.add_argument ('file', metavar='BENCHMARK', help='Benchmark file')
    p.add_argument ('--pp',
                    help='Enable default pre-processing',
                    action='store_true', default=False)
    p.add_argument ('--trace', help='Trace levels to enable',
                   default='')
    p.add_argument ('--stat', help='Print statistics', dest="stat",
                    default=False, action='store_true')
    p.add_argument ('--verbose', help='Verbose', action='store_true',
                    default=False, dest="verbose")
    p.add_argument ('--no_simp', help='Z3 simplification', action='store_false',
                    default=True, dest="simp")
    p.add_argument ('--invs', help='Additional invariants', default=None)
    p.add_argument ('--node', help='Specify top node (default:top)'
                    , dest='node', default=None)
    p.add_argument ('--cg', dest='cg', default=False, action='store_true',
                    help='Generate modular contrats')
    p.add_argument ('--smt2', dest='smt2', default=False, action='store_true',
                    help='Directly encoded file in SMT2 Format')
    p.add_argument ('--no_solving', dest='no_solving', default=False, action='store_true',
                    help='Generate only Horn clauses, i.e. do not solve')
    p.add_argument ('--validate', help='Validate generated contract with Kind2', action='store_true',
                    default=False, dest="kind2")
    p.add_argument ('--xml', help='Output result in XML format', action='store_true',
                    default=False, dest="xml")
    p.add_argument ('--no_dl', help='Disable Difference Logic (UTVPI) in SPACER', action='store_true',
                    default=False, dest="utvpi")
    pars = p.parse_args (argv)
    global verbose
    verbose = pars.verbose
    global xml
    xml = pars.xml
    return pars


def stat (key, val): stats.put (key, val)

def main (argv):
    args = parseArgs (argv[1:])
    stat ('Result', 'UNKNOWN')
    ctx = z3.Context ()
    fp = z3.Fixedpoint (ctx=ctx)
    zus = Zustre(args,ctx,fp)
    if args.no_solving:
        zus.encode()
    else:
        #z3.set_option(zustre_mode=True)
        zus.encodeAndSolve()


if __name__ == '__main__':
    res = None
    try:
        main (sys.argv)
    finally:
        if not xml: stats.brunch_print ()
    sys.exit (res)

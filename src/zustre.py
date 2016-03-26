#!/usr/bin/env python

import z3
import z3core
import stats

from z3_utils import *
from LogManager import LoggingManager
import os,subprocess,sys
import shutil
from CoCoSpec import CoCoSpec
from kind2 import Kind2
from Cex import Cex
from sfunction import SFunction
import utils


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
        self.smt2_file = None
        self.trace_file = None
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
        # if 'LUSTREC' in os.environ:
        #     lustrec = os.environ ['LUSTREC']
        if not self.isexec (lustrec):
            bin = os.path.abspath (os.path.join(root, '..', '..', 'bin'))
            lustrec = os.path.join (bin, "lustrec")
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


    def mk_horn(self):
        """generate CHC """
        lusFile = self.args.file
        self.log.info("Modular Hornification ... " + str(lusFile))
        hornDefs = None
        with utils.stats.timer('Lustre2Horn'):
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
                tracefile = lusFile_dir + base + ".traces.xml"
                self.smt2_file = smt2_file
                self.trace_file = tracefile
                self.coco.set_ctx(self.ctx)
                if self.args.cg: self.coco.parseTraceFile(tracefile)
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


    def get_raw_invs(self, preds):
        self.log.info('Getting raw invariants ... ')
        for p in preds:
            invs = fp_get_cover_delta(self.fp, p)
            print "Predicate: " + str(p)
            print "Invariants: \n\t" + str(invs)
            print "----------------------------"

    def mk_cex(self, preds):
        self.log.info("Building CEX ... ")
        cex = Cex(self.args, self.ctx, self.fp, preds, self.coco)
        return cex.get_cex_xml()

    def setSolver(self):
        """Set the configuration for the solver"""
        self.fp.set (engine='spacer')
        if self.args.stat:
            self.fp.set('print.utils.statistics',True)
        self.fp.set('use_heavy_mev',True)
        self.fp.set('pdr.flexible_trace',True)
        self.fp.set('reset_obligation_queue',False)
        self.fp.set('spacer.elim_aux',False)
        if self.args.utvpi: self.fp.set('pdr.utvpi', False)
        if self.args.tosmt:
            self.log.info("Setting low level printing")
            self.fp.set ('print.low_level_smt2',True)
        if not self.args.pp:
            self.log.info("No pre-processing")
            self.fp.set ('xform.slice', False)
            self.fp.set ('xform.inline_linear',False)
            self.fp.set ('xform.inline_eager',False)
        return

    def encodeAndSolve(self):
        """Generate horn formulas and solve"""
        self.setSolver()
        hornFormulas = self.args.file if self.args.smt2 else self.mk_horn()
        cex = None
        if not hornFormulas:
            self.log.error('Problem generating Horn formulae')
            return
        with utils.stats.timer ('Parse'):
            self.log.info('Successful Horn VCC generation ... ' + str(hornFormulas))
            q = self.fp.parse_file (hornFormulas)
        preds = utils.fp_get_preds(self.fp) # get the predicates before z3 starts playing with them
        if self.args.invs :
            lemmas = z3.parse_smt2_file (args.invs, sorts={}, decls={}, ctx=ctx)
            if z3.is_and (lemmas):
                lemmas = lemmas.children ()
            for l in lemmas:
                if verbose: print l
                fp_add_cover (self.fp, l.arg(0), l.arg(1))
        with utils.stats.timer ('Query'):
            res = self.fp.query (q[0])
            if res == z3.sat:
                utils.stat ('Result', 'CEX')
                cex = self.mk_cex(preds)
            elif res == z3.unsat:
                utils.stat ('Result', 'SAFE')
                if self.args.ri: self.get_raw_invs(preds)
                if self.args.cg: self.mk_contract (preds)
        if not self.args.save:
            self.log.debug("Cleaning up temp files ...")
            try:
                os.remove(self.smt2_file)
                os.remove(self.trace_file)
            except:
                self.log.info('No Cleaning of temp files ...')
        if self.args.xml:
            utils.stats.xml_print(self.args.node, cex)
        else:
            utils.stats.brunch_print()

    def sFunction(self):
        """Link the encoding with an externally generated Horn clause"""
        sf = SFunction(self.args)
        if sf.sanityCheck():
            utils.stat('LegacyCode', 'OK')
            self.log.info('Legacy Code is well formed ...')
            sf.getFiller()
            self.encodeAndSolve()
        else:
            utils.stat('LegacyCode', 'KO')
            self.log.error('Legacy Code Horn Clause is NOT well formed ... ')
            return


    def encode(self):
        """generate CHC and not solve"""
        hornFormulas = mk_horn()
        if not hornFormulas:
            self.log.error('Problem generating Horn formulae')
            utils.stat ('Result', 'ERR')
        else:
            utils.stat ('Result', 'SUCCESS')
        return hornFormulas



# def parseArgs (argv):
#     import argparse as a
#     p = a.ArgumentParser (description='Zustre: A verification and contract generation engine for Lustre Programs')

#     p.add_argument ('file', metavar='BENCHMARK', help='Benchmark file')
#     p.add_argument ('--pp',
#                     help='Enable default pre-processing',
#                     action='store_true', default=False)
#     p.add_argument ('--trace', help='Trace levels to enable',
#                    default='')
#     p.add_argument ('--utils.stat', help='Print utils.statistics', dest="utils.stat",
#                     default=False, action='store_true')
#     p.add_argument ('--verbose', help='Verbose', action='store_true',
#                     default=False, dest="verbose")
#     p.add_argument ('--no-simp', help='Z3 simplification', action='store_false',
#                     default=True, dest="simp")
#     p.add_argument ('--invs', help='Additional invariants', default=None)
#     p.add_argument ('--node', help='Specify top node (default:top)'
#                     , dest='node', default="top")
#     p.add_argument ('--cg', dest='cg', default=False, action='store_true',
#                     help='Generate modular contrats')
#     p.add_argument ('--smt2', dest='smt2', default=False, action='store_true',
#                     help='Directly encoded file in SMT2 Format')
#     p.add_argument ('--to-smt', dest='tosmt', default=False, action='store_true',
#                        help='Print Horn Clause in SMT Format')
#     p.add_argument ('--no-solving', dest='no_solving', default=False, action='store_true',
#                     help='Generate only Horn clauses, i.e. do not solve')
#     p.add_argument ('--validate', help='Validate generated contract with Kind2', action='store_true',
#                     default=False, dest="kind2")
#     p.add_argument ('--xml', help='Output result in XML format', action='store_true',
#                     default=False, dest="xml")
#     p.add_argument ('--save', help='Save intermediate files', action='store_true',
#                     default=False, dest="save")
#     p.add_argument ('--no_dl', help='Disable Difference Logic (UTVPI) in SPACER', action='store_true',
#                     default=False, dest="utvpi")
#     pars = p.parse_args (argv)
#     global verbose
#     verbose = pars.verbose
#     global xml
#     xml = pars.xml
#     return pars




# def main (argv):
#     args = parseArgs (argv[1:])
#     utils.stat ('Result', 'UNKNOWN')
#     ctx = z3.Context ()
#     fp = z3.Fixedpoint (ctx=ctx)
#     zus = Zustre(args,ctx,fp)
#     if args.no_solving:
#         zus.encode()
#     else:
#         #z3.set_option(zustre_mode=True)
#         zus.encodeAndSolve()


# if __name__ == '__main__':
#     res = None
#     try:
#         res = main (sys.argv)
#     finally:
#         print xml
#         if not xml: utils.stats.brunch_print ()
#     sys.exit (res)

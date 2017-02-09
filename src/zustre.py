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
from CexSF import CexSF
from sfunction import SFunction
import utils


root = os.path.dirname (os.path.dirname (os.path.realpath (__file__)))

class Zustre(object):
    def __init__(self, args, ctx, fp, lustrec_include):
        self.log = LoggingManager.get_logger(__name__)
        self.args = args
        self.lustrec_include = lustrec_include
        self.fp = fp
        self.ctx = ctx
        self.coco = CoCoSpec(self.args)
        self.smt2_file = None
        self.trace_file = None
        if self.args.xml: LoggingManager.disable_logger()
        return

    def isexec (self, fpath):
        """ check if program is executable"""
        if fpath == None: return False
        return os.path.isfile(fpath) and os.access(fpath, os.X_OK)

    def which(self,program):
        """ check locaton of a program"""
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
        """ Get the binary location for LustreC"""
        lustrec = None
        if not self.isexec (lustrec):
            bin = os.path.abspath (os.path.join(root, '..', '..', 'bin'))
            lustrec = os.path.join (bin, "lustrec")
        if not self.isexec (lustrec):
            raise IOError ("Cannot find LustreC")
        return lustrec

    def getEldarica (self):
        """ Get the binary location for Eldarica"""
        eldarica = None
        if not self.isexec (eldarica):
            eldarica = os.path.abspath (os.path.join(root, '..', '..', 'bin','eldarica', 'eld'))
        if not self.isexec (eldarica):
            raise IOError ("Cannot find Eldarica")
        return eldarica

    def getKind2 (self):
        """ Get the binary location for Kind2"""
        kind2 = None
        if not self.isexec (kind2):
            lustrec = os.path.join (root, "bin/kind2")
        if not self.isexec (kind2):
            raise IOError ("Cannot find KIND2")
        return kind2


    def mk_horn(self):
        """ Generate CHC using LustreC """
        lusFile = self.args.file
        self.log.info("Hornifiying ... " + str(lusFile))
        hornDefs = None
        with utils.stats.timer('Lustre2Horn'):
            top_node = 'top' if not self.args.node else self.args.node #TODO : check directly which node is top
            lusFile_dir = os.path.dirname(os.path.abspath(lusFile)) + os.sep
            lustrec = self.getLustreC();
            #opt_traces = ["-horn-traces"] if self.args.cg else []
            lustrec_include = self.lustrec_include + os.sep
            cmd = [lustrec, "-I", lustrec_include, "-horn", "-node", top_node, "-horn-query"] + ["-horn-traces"] + ["-d", lusFile_dir, lusFile]
            if self.args.verbose: print " ".join(x for x in cmd)
            p = subprocess.Popen(cmd, shell=False, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            hornDefs, _ = p.communicate()
            if "done" in hornDefs:
                base = (os.path.splitext(os.path.basename(lusFile)))[0]
                smt2_file = lusFile_dir + base + ".smt2"
                tracefile = lusFile_dir + base + ".traces.xml"
                self.smt2_file = smt2_file
                self.trace_file = tracefile
                self.coco.set_ctx(self.ctx)
                return smt2_file
            else:
                self.log.error(hornDefs)
                return None

    def mk_contract (self, preds):
        """ Construct CoCoSpec"""
        self.log.info("Building CoCoSpec ...")
        lusFile = self.args.file
        self.coco.parseTraceFile(self.trace_file)
        for p in preds:
            lemmas = utils.fp_get_cover_delta (self.fp, p)
            self.coco.addContract(p.decl(),lemmas)
        cocoFile_dir = os.path.dirname(os.path.abspath(lusFile)) + os.sep
        cocoFileName = cocoFile_dir + os.path.basename(lusFile) + ".coco"
        cocoSpec, emf = self.coco.mkCoCoSpec(lusFile)
        with open(cocoFileName,"w") as f:
            f.write(cocoSpec)
            self.log.info("Contract Generated in: %s", str(cocoFileName))
        return cocoFileName, emf


    def get_raw_invs(self, preds):
        """ Get unprocessed invariants """
        self.log.info('Getting raw invariants ... ')
        for p in preds:
            invs = utils.fp_get_cover_delta(self.fp, p)
            print "Predicate: " + str(p)
            print "Invariants: \n\t" + str(invs)
            print "----------------------------"


    def mk_cex(self, preds):
        """ Build CEX """
        self.log.info("Building CEX ... ")
        self.coco.parseTraceFile(self.trace_file)
        if self.args.stateflow:
            cex = CexSF(self.args, self.ctx, self.fp, preds, self.coco)
        else:
            cex = Cex(self.args, self.ctx, self.fp, preds, self.coco)
        return cex.get_cex_xml()


    def setSolver(self):
        """Set the configuration for the solver"""
        self.fp.set (engine='spacer')
        #z3.set_option(rational_to_decimal=True)
        #self.fp.set('precision',30)
        if self.args.stat:
            self.fp.set('print_statistics',True)
        if self.args.spacer_verbose:
             z3.set_option (verbose=1)
        self.fp.set('use_heavy_mev',True)
        self.fp.set('pdr.flexible_trace',True)
        self.fp.set('reset_obligation_queue',False)
        self.fp.set('spacer.elim_aux',False)
        if self.args.eldarica: self.fp.set('print_fixedpoint_extensions', False)
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
            self.log.info('Successful Horn Generation ... ' + str(hornFormulas))
            q = self.fp.parse_file (hornFormulas)
        preds = utils.fp_get_preds(self.fp) # get the predicates before z3 starts playing with them
        if self.args.invs :
            lemmas = z3.parse_smt2_file (args.invs, sorts={}, decls={}, ctx=ctx)
            if z3.is_and (lemmas):
                lemmas = lemmas.children ()
            for l in lemmas:
                if self.args.verbose: print l
                fp_add_cover (self.fp, l.arg(0), l.arg(1))
        contract_file, emf_file = None, None
        with utils.stats.timer ('Query'):
            res = self.fp.query (q[0])
            if res == z3.sat:
                utils.stat ('Result', 'CEX')
                cex = self.mk_cex(preds)
            elif res == z3.unsat:
                utils.stat ('Result', 'SAFE')
                if self.args.ri: self.get_raw_invs(preds)
                if self.args.cg:
                    try:
                        contract_file, emf_file = self.mk_contract (preds)
                    except Exception as e:
                        print e
                        self.log.warning('Failed to generate CoCoSpec')
        if not self.args.save:
            self.log.debug("Cleaning up temp files ...")
            try:
                os.remove(self.smt2_file)
                os.remove(self.trace_file)
            except:
                self.log.info('No Cleaning of temp files ...')
        if self.args.xml:
            utils.stats.xml_print(self.args.node, cex, contract_file, emf_file)
        else:
            utils.stats.brunch_print()

    def eldarica(self):
        """Generate horn formulas and solve with Eldarica"""
        self.setSolver()
        hornFormulas = self.mk_horn()
        if not hornFormulas:
            self.log.error('Problem generating Horn formulae')
            return
        with utils.stats.timer ('Parse'):
            self.log.info('Successful Horn VC generation ... ' + str(hornFormulas))
            q = self.fp.parse_file (hornFormulas)
            utils.stats.stop('Parse')
            lusFile = self.args.file
            lusFile_dir = os.path.dirname(os.path.abspath(lusFile)) + os.sep
            base = (os.path.splitext(os.path.basename(lusFile)))[0]
            smt2_name = lusFile_dir + base + "_puresmt2.smt2"
            with open(smt2_name, 'w') as sf:
                puresmt2 = self.fp.to_string(q)
                sf.write(puresmt2)
            self.log.info("Running Eldarica ... ")
            with utils.stats.timer('Eldarica'):
                 cmd = [self.getEldarica(), '-ssol', '-lbe', smt2_name]
                 p = subprocess.Popen(cmd, shell=False, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                 eldaricaOut, _ = p.communicate()
                 if 'sat' in eldaricaOut:
                     utils.stat ('Result', 'SAFE')
                 elif 'unsat' in eldaricaOut:
                     utils.stat('Result', 'CEX')
                 else:
                     utils.stat('Result', 'UNKNOWN')
            utils.stats.stop('Eldarica')
            if self.args.xml:
                utils.stats.xml_print(self.args.node, cex, None)
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
        hornFormulas = self.mk_horn()
        if not hornFormulas:
            self.log.error('Problem generating Horn formulae')
            utils.stat ('Result', 'ERR')
        else:
            utils.stat ('Result', 'SUCCESS')
        return hornFormulas

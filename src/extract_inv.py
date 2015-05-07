#!/usr/bin/python
#
# A prototype tool/module for extraction of BV invariants from LA certificates
#
# (c) Anton Belov, 2013

from __future__ import print_function
import latobv
import bv2aig
import misper
import sys
import os
import tempfile
import re
import z3

class Assum:
    '''Aggregates the information pertaining to an assumption'''
    def __init__(self, name="", pre=None):
        self.name = name
        self.pre = pre       # True when pre, False when post
        self.pair = None     # the matching assumption
        self.in_aig = None   # True when the assumption is in AIG after prepro
        self.in_mis = None   # True when the assumption is in MIS

    def prt(self, f=sys.stdout):
        print("%s (pre=%s, match_name=%s, in_aig=%s, in_mis=%s)" % 
              (self.name, self.pre, self.pair.name if self.pair else "none",
               self.in_aig, self.in_mis), file=f)
        
    def is_init(self):
        '''Returns true if the assumption is for the init location'''
        return (self.pre and self.pair == None)
    
    def is_error(self):
        '''Returns true if the assumption is for the error location'''
        return (not self.pre and self.pair == None)


class InvExtractor:
    '''Aggregates all the functionality related to the extraction
    
    The pipeline is as follows:
        LA certificate -> [latobv] -> BV -> [bv2aig] -> AIG -> [misper] -> INV
        [latobv] stage may be skipped if BV file is given as input
    
    Configuration parameters (members):
        self.verbose = 1            # verbosity level
        self.width = 32             # bitwidth for LA -> BV conversion
        self.skip = False           # if True, skip LA -> BV conversion
        self.btor_rwl = 3           # rewrite level in boolector in bv2aig
        self.abc = False            # use ABC stage in bv2aig
        self.abc_pipeline = "dc2 -v; dch; dc2 -v; &get; &fraig; &put; dch -v; dc2 -v" 
        self.muser_opts = "-prog -order 4 -v 3"  # options for muser-2
        self.add_missing = True     # if True, treat missing assumptions as part
                                    # of the invariant
        self.inv_file_name = None   # if not None, the path to SMT2 invariant
    '''
    def __init__(self, aiger_root, btor_root, abc_path, muser2_path):
        '''The aiger_root and btor_root are directories; abc_path and muser2_path
            are executables'''
        if not os.path.exists(aiger_root):
            raise ValueError("aiger directory is not found at %s" % aiger_root)
        if not os.path.exists(btor_root):
            raise ValueError("boolector directory is not found at %s" % btor_root)
        if not os.path.exists(abc_path):
            raise ValueError("abc executable is not found at %s" % abc_path)
        if not os.path.exists(muser2_path):
            raise ValueError("muser2 executable is not found at %s" % muser2_path)
        self.verbose = 1            # verbosity level
        self.width = 32             # bitwidth for LA -> BV conversion
        self.skip = False
        self.btor_rwl = 3           # rewrite level in boolector in bv2aig
        self.abc = False            # use ABC stage in bv2aig
        self.abc_pipeline = "dc2 -v; dch; dc2 -v; &get; &fraig; &put; dch -v; dc2 -v"
        self.muser_opts = "-prog -order 4 -v 3"  # options for muser-2
        self.add_missing = True
        self.la2bv = latobv.LaToBvExt()
        self.bv2aig = bv2aig.Bv2aig(aiger_root, btor_root, abc_path)
        self.misper = misper.Misper(aiger_root, muser2_path)
        self.init_file_name = None
        self.bv_file_name = None
        self.aig_file_name = None
        self.inv_file_name = None
        self.a_map = {}              # assumption map: key = name, value = Assum
        self.a_init = self.a_error = None # to store init and error
        self.test = False

    def __parse_cert(self):
        '''Parses the input certificate to extract the pre/post assumptions'''
        for line in open(self.in_file_name):
            if line.startswith("(check-sat"): # pre's
                for name in re.findall("pre[^(\s|))]+", line):
                    self.a_map[name] = Assum(name, True)
            elif re.match(";\s*\(post-assumptions", line):
                for name in re.findall("post[^(\s|))]+", line):
                    if not name.startswith("post-assumptions"):
                        self.a_map[name] = Assum(name, False)
        if len(self.a_map.items()) == 0:
            raise ValueError("couldn't find pre/post assumptions in the input certificate")
        # match them up; and check correctness
        inits = errors = pairs = 0
        for name in self.a_map.keys():
            if name.startswith("pre!"):
                try:
                    self.a_map[name].pair = self.a_map[name.replace("pre!", "post!")]
                    pairs += 1
                except KeyError:
                    self.a_init = self.a_map[name]
                    inits += 1
            else:
                assert name.startswith("post!"), "assumption names must start with pre! or post!"
                try:
                    self.a_map[name].pair = self.a_map[name.replace("post!", "pre!")]
                except KeyError:
                    self.a_error = self.a_map[name]
                    errors += 1
        #self.print_a_map()
        if inits != 1:
            raise ValueError("input certificate is expected to have exactly 1 "
                             "assumption for init location (found " + str(inits) +")")
        if errors != 1:
            raise ValueError("input certificate is expected to have exactly 1 "
                             "assumption for error location (found " + str(errors) +")")
        if self.verbose >= 1:
            print("[extract_inv] input certificate has %d pairs of lemmas, "
                  "plus 1 init location lemma, and 1 error location lemma" % 
                  (len(self.a_map.keys())/2-1))
            if self.verbose >= 2: 
                print("[extract_inv] %d assumptions in the input certificate: " % len(self.a_map.keys()), end="")
                for name in self.a_map.keys(): print(name, end=" ")
                print()
        # done

    def __update_a_map_aig(self):
        '''Updates the in_aig values in the assumption map, based on the content
        of the AIG file; returns the number of remaining assumptions'''
        (matched, unmatched) = self.bv2aig.get_selectors(self.aig_file_name)
        r_list = matched.keys()
        r_list += matched.values()
        r_list += unmatched
        removed = []
        for name in r_list: self.a_map[name].in_aig = True
        for a in self.a_map.values(): 
            if a.in_aig != True: 
                a.in_aig = False
                removed.append(a.name)
        if self.verbose >= 1:
            print("[extract_inv] %d out of %d initial assumptions are missing from the AIG" % 
                  (len(removed), len(self.a_map.keys())))
            if self.verbose >= 2:
                print("[extract_inv] missing assumptions: ", end="")
                for name in removed: print(name, end=" ")
                print()
        return len(self.a_map.keys()) - len(removed)

    def __update_a_map_mis(self, mis):
        '''Updates the in_mis values in the assumption map, given the list of 
        inductive assumptions'''
        for name in mis: self.a_map[name].in_mis = True
        for a in self.a_map.values():
            if a.in_mis != True: a.in_mis = False
        if self.verbose >= 1:
            print("[extract_inv] MIS contains %d assumptions" % len(mis))
            if self.verbose >= 2 and len(mis) > 0:
                print("[extract_inv] MIS assumptions: ", end="")
                for name in mis: print(name, end=" ")
                print()

    def __update_a_map_add_missing(self):
        '''Adds all assumptions that are missing from AIG as MIS'''
        mis = []
        for a in self.a_map.values():
            if not a.in_aig: a.in_mis = True
            if a.in_mis: mis.append(a.name)
        if self.verbose >= 1:
            print("[extract_inv] added assumptions missing from AIG, MIS contains %d assumptions" % len(mis))
            if self.verbose >= 2 and len(mis) > 0:
                print("[extract_inv] MIS assumptions: ", end="")
                for name in mis: print(name, end=" ")
                print()

    def __cleanup_bv(self, bv_file_name):
        '''Runs through the bv_file, and replaces (check-sat ...) with (check-sat)
        so that boolector doesn't complain'''
        new_bv_name = tempfile.mkstemp(".smt2", text = True)[1]
        out = open(new_bv_name, "w")
        for line in open(bv_file_name):
            if line.startswith("(check-sat"): line = "(check-sat)\n"
            print(line, file=out, end='')
        out.close()
        return new_bv_name
                        
    def print_a_map(self, f=sys.stdout):
        '''Prints out the assumption map'''
        print("  init_loc: %s (in_aig=%s, in_mis=%s)" % 
              (self.a_init.name, self.a_init.in_aig, self.a_init.in_mis),file=f)
        for a in self.a_map.values():
            if a.pre and not a.is_init():
                print("  %s (in_aig=%s, in_mis=%s) -- %s (in_aig=%s, in_mis=%s)" %
                      (a.name, a.in_aig, a.in_mis, a.pair.name, a.pair.in_aig, a.pair.in_mis),
                      file=f)
        print("  error_loc: %s (in_aig=%s, in_mis=%s)" % 
              (self.a_error.name, self.a_error.in_aig, self.a_error.in_mis),file=f)

    def report_mis_status(self):
        '''Prints out the summary status, based on the content of a_map'''
        if not self.a_init.in_mis:
            raise Exception("initial location is not in MIS")
        init_lemmas = len(self.a_map.keys())/2-1
        mis_lemmas = 0
        for a in self.a_map.values():
            if not a.is_init() and not a.is_error() and a.pre and a.in_mis: mis_lemmas += 1
        if self.verbose >= 1:
            print("[extract_inv] invariant contains %d out of %d initial pairs of lemmas" %
                  (mis_lemmas, init_lemmas))
            if self.a_error.in_mis:
                print("[extract_inv] invariant also contains the error location lemma")
            else:
                print("[extract_inv] invariant does NOT contain the error location lemma")
                
    def write_invariant(self, out=sys.stdout):
        '''Writes out the SMT2 invariant, i.e. the BV file plus the MIS assertions'''
        for line in open(self.bv_file_name):
            if not line.startswith("(check-sat"):
                print(line, end="", file=out)
        # now add all mis assertions
        for a in self.a_map.values():
            print("(assert %s)" % (a.name if (a.pre == a.in_mis) else "(not "+a.name+")"), file=out)
        print("(check-sat)", file=out)

    def test_invariant(self):
        '''Generates the SMT2 invariant (if self.inv_file_name == None), and 
        runs z3 on it; returns True if z3 returns UNSAT'''
        if self.verbose >= 1:
            print("[extract_inv] testing the computed invariant for UNSAT")
        if self.inv_file_name is not None:
            inv_file_name = self.inv_file_name
        else:
            inv_file_name = tempfile.mkstemp(".smt2", text = True)[1]
            inv_file = open(inv_file_name, "w")
            self.write_invariant(inv_file)
            inv_file.close()
        ctx = z3.Context()
        solver = z3.Solver(ctx=ctx)
        solver.add(z3.parse_smt2_file(inv_file_name, ctx=ctx))
        res = (solver.check().r == -1)
        if self.verbose >= 1:   
            print("[extract_inv] test %s" % ("PASSED" if res else "FAILED"))
        return res

    def write_answer(self, out=sys.stdout):
        '''Writes out the answer in DIMACS-ish format'''
        if self.a_error.in_mis:
            print("s SAFE", file=out)
        else:
            print("s UNKNOWN", file=out)
        print("v", end=" ", file=out)
        for a in self.a_map.values():
            if a.in_mis: print(a.name, end=" ", file=out)
        print(file=out)
                
    def run(self, in_file_name):
        '''Runs the pipeline; returns True if the MIS is safe, False otherwise'''
        if self.verbose >= 1:
            print("[extract_inv] input file: " + in_file_name)
            print("[extract_inv] configuration: ")
            print("[extract_inv]   width = %d" % self.width)
            print("[extract_inv]   skip = %r" % self.skip)
            print("[extract_inv]   btor_rwl = %d" % self.btor_rwl)
            print("[extract_inv]   add_missing = %d" % self.add_missing) 
            print("[extract_inv]   abc = %r" % self.abc)
            print("[extract_inv]   abc_pipeline = '%s'" % self.abc_pipeline)
            print("[extract_inv]   muser_opts = '%s'" % self.muser_opts)
            if self.inv_file_name:
                print("[extract_inv] output invariant file: " + self.inv_file_name)
        self.in_file_name = in_file_name
        self.__parse_cert()
        if self.skip:
            if self.verbose >= 1: print("[extract_inv] skipping latobv")
            self.bv_file_name = self.in_file_name
        else:
            if self.verbose >= 1: print("[extract_inv] running latobv")
            self.bv_file_name = tempfile.mkstemp(".smt2", text = True)[1]
            self.la2bv.convert(self.in_file_name, self.bv_file_name, self.width)
        self.bv_file_name = self.__cleanup_bv(self.bv_file_name)
        if self.verbose >= 1: print("[extract_inv] running bv2aig")
        self.bv2aig.abc = self.abc
        self.bv2aig.abc_pipeline = self.abc_pipeline
        self.bv2aig.btor_rwl = self.btor_rwl
        self.bv2aig.verbose = self.verbose
        self.aig_file_name = tempfile.mkstemp(".aig", text = True)[1]
        self.bv2aig.convert(self.bv_file_name, self.aig_file_name)
        num_left = self.__update_a_map_aig()
        if num_left:
            if self.verbose >= 1: print("[extract_inv] running misper")
            self.misper.verbose = self.verbose
            self.misper.muser_opts = self.muser_opts
            self.misper.load_aig(self.aig_file_name)
            (pres, posts) = self.misper.compute()
            pres = [a.name for a in pres]
            posts = [a.name for a in posts]
            #print("[extract_inv] computed MIS of size %d lemmas:" % len(posts))
            #self.misper.prt_state() # TEMP: need to decide how to proceed
            #self.misper.write_smt2()
        else:
            if self.verbose >= 1: print("[extract_inv] skipping misper")
            (pres, posts) = ([], [])
        self.__update_a_map_mis(pres + posts)
        if self.add_missing: self.__update_a_map_add_missing()
        self.report_mis_status()
        if self.inv_file_name: 
            f = open(self.inv_file_name, "w")
            self.write_invariant(f)
            f.close()
            if self.verbose >= 1: print("[extract_inv] wrote invariant to %s" % self.inv_file_name)
        if self.test: self.test_invariant()
        if not self.a_init.in_mis:
            raise Exception("initial location is not in MIS")
        if self.verbose >= 1: self.write_answer()
        return self.a_error.in_mis
        
# Entry point for external callers
if __name__ == "__main__":
    def parseArgs(argv):
        import argparse as a
        p = a.ArgumentParser(description="BV invariant extractor",
                             formatter_class=a.ArgumentDefaultsHelpFormatter)
        p.add_argument ("in_file", type=str, 
                        help="LA (or BV) formula in SMT2 format")
        p.add_argument ("-v", "--verb", type=int, 
                        help="verbosity level (0,1,2)", default=1)
        p.add_argument ("-w", "--width", type=int,
                        help="bit-width for LA to BV conversion", 
                        default=32)
        p.add_argument("-s", "--skip",
                       help="skip the LA to BV conversion, input should be BV",
                       action='store_true', default=False)
        p.add_argument ("-b", "--btorrwl", type=int,
                        help="rewrite level in boolector (0-3)", 
                        default=3)
        p.add_argument ("-a", "--abc",
                        help="use ABC stage", 
                        action='store_true', default=False)
        p.add_argument("-n", "--no_missing",
                        help="by default the assumptions that are missing from \
                             AIG are added to the invariant; specifying this \
                             option disables this addition",
                        action='store_true', default=False)
        p.add_argument ("--abccmd", type=str, 
                        help="the pipeline of ABC commands to use (enclosed in quotes);\
                              add -v and set --verb 2 to see what ABC is doing", 
                        default='dc2 -v; dch; dc2 -v; &get; &fraig; &put; dch -v; dc2 -v')
        p.add_argument ("--museropts", type=str, 
                        help="the options for muser-2 (enclosed in quotes)",
                        default='-prog -order 4 -v 3')
        p.add_argument ("--mroot", type=str, 
                        help="the path to misp project root, assumes that\
                              aiger package is in misp/tools/aiger, \
                              boolector package is in misp/tools/boolector, \
                              abc executable is at misp/tools/abc/abc, \
                              muser-2 executable is at misp/tools/muser-2/muser-2",
                        default="~/MyRoot/School/research/misp/misp")
        p.add_argument("--inv-file", type=str,
                        help="if specified: the file to output the invariant as\
                              SMT2 formula, the invariant should be UNSAT.",
                        default = None)
        p.add_argument("-t", "--test",
                       help="test the UNsatisfiability of the invariant with z3",
                       action='store_true', default=False)
        return p.parse_args (argv)
    # go ...
    args = parseArgs(sys.argv[1:])
    try:
        ie = InvExtractor(args.mroot + "/tools/aiger",
                          args.mroot + "/tools/boolector",
                          args.mroot + "/tools/abc/abc",
                          args.mroot + "/tools/muser-2/muser-2")
        ie.verbose = args.verb
        ie.width = args.width
        ie.skip = args.skip
        ie.btor_rwl = args.btorrwl
        ie.abc = args.abc
        ie.abc_pipeline = args.abccmd
        ie.muser_opts = args.museropts
        ie.add_missing = not args.no_missing
        ie.inv_file_name = args.inv_file
        ie.test = args.test
        ie.run(args.in_file)
    except IOError as e:
        print("[extract_inv] ERROR: %r on %s" % (e, e.filename))
    except Exception as e:
        if (e.message): print("[extract_inv] ERROR: " + e.message)
        else: print("[extract_inv] ERROR: %r " % e)
        

from LogManager import LoggingManager
import pprint
from z3_utils import *
import textwrap
import xml.etree.ElementTree as ET
from z3_utils import *
from cocoprinter import *
from lustreAnnotation import LustreAnnot



debug_coco = ("""contract %s (%s) returns (%s);
 %s
 let
   -- INITIAL STATES Contract
   ensure %s;

    -- TRANSITION RELATION Contract
    ensure %s;
 tel
 """)

validate_coco = ("""contract %s (%s) returns (%s);
%s
let
   ensure    (%s)
          -> (%s);
tel
""")

class CoCoSpec(object):

    def __init__(self, args):
        #self.tf = trace_file
        self.ctx = None
        self._log = LoggingManager.get_logger(__name__)
        self.contract_dict = {}
        self.local_vars = {}
        self.varMappingAll = {}
        self.varMapping = {}
        self.varMappingTypes = {}
        self.z3MapVar = []
        self.do_simp = args.simp
        self.verbose = args.verbose
        self.kind2 = args.kind2
        self.pp = pprint.PrettyPrinter(indent=4)
        self.z3Types = {"Int":z3.Int, "Real": z3.Real,"Bool":z3.Bool}


    def log (self, method, msg):
        print "====== (Start) " + method + " ======="
        self.pp.pprint(msg)
        print "====== (End) " + method + " ======="

    def set_ctx (self, ctx): self.ctx = ctx

    def addContract(self, pred, inv):
        if self.verbose: self.log("addContact raw invariants", inv)
        tac = z3.Tactic('simplify', self.ctx)
        #s = tac.apply(inv)
        simplified =  z3.simplify(inv)

        if str(pred) not in ["ERR", "INIT_STATE", "MAIN"]:
            simplified = self.coco_simplify(z3.substitute (simplified, *self.z3MapVar))
            if self.verbose: self.log("After simplification", simplified)
            self.contract_dict.update({pred:simplified})
        return

    def coco_simplify (self, e):
        # Teme TODO
        return z3.simplify (e)


    def ppContract(self):
        self.pp.pprint(self.contract_dict)

    def mkFormulae(self, form):
        if self.do_simp:
            tac = CoCoTac(self.ctx, self.verbose)
            if self.verbose: self.log("Before Tac", form)
            form_str = ""
            try:
                form_str = printCoCo(tac.tac(form))
                if self.verbose: self.log("After Tac", form_str)
                return "\n\t" + form_str
            except Exception as e:
                self._log.warning("Tactics was not applied")
                if self.verbose: self.log("Reason:" , str(e))
                return "\n\t" + printCoCo(form)
        else:
            if self.verbose: self.log("No Tac ", form)
            return "\n\t" + printCoCo(form)

    def mkCoCoSpec(self, lusFile):
        coco_dict = {}
        is_contract_profile = False
        tracefile = (lusFile.split(".")[0]) + ".traces.xml"
        for pred,form in self.contract_dict.iteritems():
            if "_init" in str(pred):
                node_name = str(pred).split("_init")[0]
                try:
                    inv = coco_dict[node_name]
                    inv.update({"init":form})
                except:
                    coco_dict.update({str(node_name):{"init":form}})
            elif "_step" in str(pred):
                node_name = str(pred).split("_step")[0]
                try:
                    inv = coco_dict[node_name]
                    inv.update({"step":form})
                except:
                    coco_dict.update({node_name:{"step":form}})
            else:
                self._log.warning("pred: " + str(pred) + "with no init or step")
                node_name = str(pred)
                coco_dict.update({node_name:{"aux":form}})
        all_contract = "-- CoCoSpec --\n"
        for node, form in coco_dict.iteritems():
            profile = self.contractProfile(node) if is_contract_profile else "() returns ();"
            outputList = (self.varMappingAll[node])["output"]
            inp = self.mkProfileInOut((self.varMappingAll[node])["input"])
            out = self.mkProfileInOut(outputList)
            local = self.mkProfileLocal((self.varMappingAll[node])["local_init"], outputList)
            pattern_coco = validate_coco if self.kind2 else debug_coco
            try:
                # this is case when we don't have init and step
                aux_form = self.mkFormulae(form["aux"])
                contract =  pattern_coco % (node, inp, out, local, aux_form, "")
            except Exception as e:
                init_form = self.mkFormulae(form["init"])
                step_form = self.mkFormulae(form["step"])
                contract =  pattern_coco % (node, inp, out, local, init_form, step_form)
            all_contract += contract + "\n"
            if self.verbose: print "==== CoCo ===  \n" + contract + "\n===== CoCo ====="
        if self.kind2:
            self._log.info("Attaching the Lustre file for Kind2 validation")
            lusAnnot = LustreAnnot()
            if lusAnnot.parseFile(lusFile):
                self._log.info("Lustre parsing OK")
                annotated_lus = lusAnnot.annotate()
                all_contract += " -- Lustre Nodes --\n" + annotated_lus
            else:
                self._log.warning("Lustre parsing NOT OK")
                assert False
        return all_contract

    def mkProfileInOut(self, inpList):
        return ";".join("%s:%s" % (v,t.lower()) for (v,t) in inpList)

    def mkProfileLocal(self, localList, outputList):
        # make sure you don't print more than one local vars
        localList = list(set(localList))
        if localList != []:
            local = ""
            for var, typ in localList:
                if (var,typ) not in outputList: # print only local vars which are not in the outputList
                    var_tmp = " ".join(var.split())
                    local += var.replace("pre", "") + ":" + typ.lower() + "; "
            return "var " + local if local != "" else local
        else:
            return ""


    def mkZ3Vars(self):
        for k,v in self.varMappingTypes.iteritems():
            strip_v = ((v.replace("(pre","")).replace(")","")).strip() if "(pre" in v else v
            new_v ="pre("+strip_v+")" if "(pre" in v else v
            z3varHorn = self.z3Types[k[1]](k[0], self.ctx)
            z3varLus =  self.z3Types[k[1]](new_v, self.ctx)
            self.z3MapVar.append((z3varHorn,z3varLus))
        return


    def parseTraceFile(self, xmlTraceFile):
        self._log.info("Parsing Trace file: %s" % xmlTraceFile)
        try:
            xmldoc = ET.parse(xmlTraceFile)
            node_dict = {}
            for node in xmldoc.iter("Node"):
                node_name = node.attrib.get("name")
                inp, output, local_init, local_step = {}, {}, {}, {}
                for n in node.iter("input"):
                    horn = (n.attrib.get("name")).split(" | ")
                    typ = (n.attrib.get("type")).split(" | ")
                    lus = (n.text).split(" | ")
                    inp = zip(lus, typ)
                    self.varMapping.update(dict(zip(horn,lus)))
                    self.varMappingTypes.update(dict(zip(zip(horn,typ),lus)))
                for n in node.iter("output"):
                    horn = (n.attrib.get("name")).split(" | ")
                    typ = (n.attrib.get("type")).split(" | ")
                    lus = (n.text).split(" | ")
                    output =  zip(lus, typ)
                    self.varMapping.update(dict(zip(horn,lus)))
                    self.varMappingTypes.update(dict(zip(zip(horn,typ),lus)))
                for n in node.iter("localInit"):
                    if n.text:
                        horn = (n.attrib.get("name")).split(" | ")
                        typ = (n.attrib.get("type")).split(" | ")
                        lus = (n.text).split(" | ")
                        local_init = zip(lus, typ)
                        self.varMapping.update(dict(zip(horn,lus)))
                        self.varMappingTypes.update(dict(zip(zip(horn,typ),lus)))
                for n in node.iter("localStep"):
                    if n.text:
                        horn = (n.attrib.get("name")).split(" | ")
                        typ = (n.attrib.get("type")).split(" | ")
                        lus = (n.text).split(" | ")
                        local_step = zip(lus, typ)
                        self.varMapping.update(dict(zip(horn,lus)))
                        self.varMappingTypes.update(dict(zip(zip(horn,typ),lus)))
                node_dict.update({node_name:{"input":inp,"output":output, "local_init":local_init, "local_step":local_step}})
            self.varMappingAll.update(node_dict)
            pp = pprint.PrettyPrinter(indent=4)
            #pp.pprint(self.varMappingAll)
            #pp.pprint(self.varMapping)
            #pp.pprint(self.varMappingTypes)
            #making pairs of vars for the subsitution
            self.mkZ3Vars()
            #pp.pprint(self.z3MapVar)

        except Exception as e:
            self._log.warning(str(e))




class CoCoTac(object):

    def __init__(self,ctx, verbose):
        self.verbose = verbose
        self.ctx = ctx
        self.pp = pprint.PrettyPrinter(indent=4)

    #TODO, laziness and ugly
    def log (self, method, msg):
        print "====== (Start) " + method + " ======="
        self.pp.pprint(msg)
        print "====== (End) " + method + " ======="

    def is_iff (self, expr):
        return z3.is_app_of (expr, z3.Z3_OP_IFF)

    def is_not (self, expr):
        return z3.is_app_of (expr, z3.Z3_OP_NOT)

    def is_or (self, expr):
        return z3.is_app_of (expr, z3.Z3_OP_OR)

    def is_and (self, expr):
        return z3.is_app_of (expr, z3.Z3_OP_AND)

    def nnf (self, expr):
        nnf_formula = z3.Tactic ('nnf',self.ctx) .apply(expr)
        if nnf_formula:
            return nnf_formula
        else:
            return expr


    def mk_and(self, expr_list):
        conjunct = [printCoCo(x) for x in expr_list]
        no_new_line = [x.rstrip() for x in conjunct]
        stripped = [textwrap.fill(x, 40) for x in no_new_line]
        return " and ".join(map(str,stripped))


    def tac2(self, expr):
        "tactic to transform [a v b] into [not(a) => b]"
        if self.verbose: self.log("TAC-2 Before", str(expr))
        lhs_list = self.nnf(z3.Not(expr.arg(0)))[0]
        rhs_list = expr.children()[1:]
        rhs = rhs_list[0] if len(rhs_list)==1 else z3.Or(rhs_list,self.ctx)
        lhs = lhs_list[0] if len(lhs_list)==1 else z3.And(lhs_list,self.ctx)
        simp = z3.Implies(lhs,rhs)
        if self.verbose: self.log("TAC-2 After", str(simp))
        return simp


    def tac1(self, expr):
        "tactic to transform [not a = b] into [a = nnf(not b)]"
        if self.verbose: self.log("TAC-1 Before", str(expr))
        not_lhs = (expr.arg(0)).arg(0)
        rhs_list = self.nnf(z3.Not(expr.arg(1), self.ctx))[0]
        rhs_ctx = [z3.And(x, self.ctx) for x in rhs_list] # HUGE HACK
        rhs = z3.simplify(z3.And(rhs_ctx,self.ctx))
        simp = (not_lhs == rhs)
        if self.verbose: self.log("TAC-1 After", str(simp))
        return simp


    def tac(self, expr):
        if self.is_iff(expr) and self.is_not(expr.arg(0)):
            simplified = self.tac1(expr)
            return simplified
        elif self.is_and(expr):
            simp_formula = []
            for dis in get_conjuncts(expr):
                if self.is_or(dis):
                    simp = self.tac2(dis)
                    simp_formula.append(simp)
                else:
                    simp_formula.append(dis)
            return z3.And(simp_formula, self.ctx)
        else:
            return expr

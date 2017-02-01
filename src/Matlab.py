from cocoprinter import *
import os,subprocess,sys
import shutil

lustre_matlab = ("""node %s (%s) returns (inv:bool);
let
   inv = %s;
tel
""")

root = os.path.dirname (os.path.dirname (os.path.realpath (__file__)))

class Matlab(object):
    def __init__(self, varMapping, req_ens, coco_dict):
        self.varMapping = varMapping
        self.req_ens = req_ens
        self.coco_dict = coco_dict
        return

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

    def mk_emf(self, matlab_contract):
        """ Generate Embedded Matlab using LustreC """
        lusFile_dir = os.path.dirname(os.path.abspath(matlab_contract)) + os.sep
        lustrec = self.getLustreC();
        cmd = [lustrec, "-emf"] + ["-d", lusFile_dir, matlab_contract]
        p = subprocess.Popen(cmd, shell=False, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        emf, _ = p.communicate()
        return "done" in emf



    def mkMatlab(self, lusFile):
        """ Build the whole CoCoSpec """
        all_nodes = "-- CoCoSpec --\n"
        for node, form in self.coco_dict.iteritems():
            outputList = (self.varMapping[node])["output"]
            inp = self.mkProfileInOut((self.varMapping[node])["input"])
            out = self.mkProfileInOut(outputList)
            local = self.mkProfileLocal((self.varMapping[node])["local_init"], outputList)
            # Currently ouputing only input/output contract and not local flows
            if local == "":
                ens = self.req_ens[node]['ens']
                node_out = lustre_matlab % (node, inp + "; " + out, ens)
                all_nodes += node_out + "\n"
            cocoFile_dir = os.path.dirname(os.path.abspath(lusFile)) + os.sep
            matlab_contract =cocoFile_dir + os.path.basename(lusFile) + ".matlab.lus"
            with open(matlab_contract,"w") as f:
                 f.write(all_nodes)
            return self.mk_emf(matlab_contract)

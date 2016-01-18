
[![Code Issues](http://www.quantifiedcode.com/api/v1/project/f01b6e8e42264a9db43a4221e4ebdb51/badge.svg)](http://www.quantifiedcode.com/app/project/f01b6e8e42264a9db43a4221e4ebdb51)
[![Build Status](https://travis-ci.org/coco-team/zustre.svg)](https://travis-ci.org/coco-team/zustre)

# Zustre #

Zustre is a modular SMT-based PDR-style verification engine for Lustre programs. It is also an engine to generate assume-guarantee style contract.

##License##
Zustre is distributed under a modified BSD license. See [LICENSE](LICENSE) for details.

### Dependencies ###

* [LustreC (Lustre compiler)](https://github.com/coco-team/lustrec)
* [SPACER (PDR engine)](http://spacer.bitbucket.org/)
* Python v. 2.7.


##Compilation##

*  Build separately [LustreC](https://github.com/coco-team/lustrec) 
* `cd zustre ; mkdir build ; cd build`
* `cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=run -DLUSTREC_EXECUTABLE=LUSTREC_BIN ../ ` where `LUSTREC_BIN` is the directory containing the lustrec binary.
* `cmake --build .` to build zustre
* `cmake --build . --target install` to install everything in `run` directory
* `cmake --build . --target package` to package everything.

Zustre and dependencies are installed in `build/run`


## Usage ##
* To simply verify Lustre code:
```
>  ./build/run/bin/zustre [LUSTRE_FILE] --node [OBSERVER NODE (default: top)]
```

* To generate CoCoSpec contract of Lustre code:
```
> ./build/run/bin/zustre [LUSTRE_FILE] --cg --node [OBSERVER NODE (default: top)]
```

### Options ###
* -h, --help         show this help message and exit
* --pp               Enable default pre-processing
* --trace TRACE      Trace levels to enable
* --stat             Print statistics
* --verbose          Verbose
* --no-simp          Z3 simplification
* --invs INVS        Additional invariants
* --node NODE        Specify top node (default:top)
* --cg               Generate modular contrats
* --smt2             Directly encoded file in SMT2 Format
* --no-solving       Generate only Horn clauses, i.e. do not solve
* --xml              Output result in XML format
* --save             Save intermediate files
* --no-dl            Disable Difference Logic (UTVPI) in SPACER
* --timeout TIMEOUT  Timeout


### Contact ###
* Temesghen Kahsai (NASA Ames / CMU)
* Arie Gurfinkel (SEI / CMU)

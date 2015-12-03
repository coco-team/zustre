
[![Code Issues](http://www.quantifiedcode.com/api/v1/project/f01b6e8e42264a9db43a4221e4ebdb51/badge.svg)](http://www.quantifiedcode.com/app/project/f01b6e8e42264a9db43a4221e4ebdb51)

# Zustre #

Zustre is a modular SMT-based PDR-style verification engine for Lustre programs. It is also an engine to generate assume-guarantee style contract.


### Dependencies ###

* [LustreC (Lustre compiler)](https://github.com/coco-team/lustrec)
* [SPACER (PDR engine)](http://spacer.bitbucket.org/)
* Python v. 2.7.

#License#
Zustre is distributed under a modified BSD license. See [license.txt](license.txt) for details.

#Compilation#

*  Build separately [LustreC](https://github.com/coco-team/lustrec) 
* `cd zustre ; mkdir build ; cd build`
* `cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=run -DLUSTREC_EXECUTABLE=LUSTREC ../ ` where `LUSTREC_BIN` is the directory containing the lustrec binary.
* `cmake --build .` to build zustre
* `cmake --build . --target install` to install everything in `run` directory
* `cmake --build . --target package` to package everything.

Zustre and dependencies are installed in `build/run`


### How to use Zustre? ###
* To simply verify Lustre code:
```
>  ./build/run/bin/zustre [LUSTRE_FILE] --node [OBSERVER NODE (default: top)]
```

* To generate CoCoSpec contract of Lustre code:
```
> python src/zustre.py [LUSTRE_FILE] --cg --node [OBSERVER NODE (default: top)]
```

### Options ###

* --xml : Output result in xml format 

### Contact ###
* Temesghen Kahsai (NASA Ames / CMU)
* Arie Gurfinkel (SEI / CMU)

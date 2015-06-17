
[![Code Issues](http://www.quantifiedcode.com/api/v1/project/f01b6e8e42264a9db43a4221e4ebdb51/badge.svg)](http://www.quantifiedcode.com/app/project/f01b6e8e42264a9db43a4221e4ebdb51)

# Zustre #

Zustre is a modular SMT-based PDR-style verification engine for Lustre programs. It is also an engine to generate assume-guarantee style contract.


### Dependencies ###

* [LustreC (Lustre compiler)](https://github.com/lememta/lustrec)
* [SPACER (PDR engine)](http://spacer.bitbucket.org/)
* Python v. 2.7.

### Build ###

* Build separately [LustreC](https://bitbucket.org/lememta/lustrec) and [SPACER](http://spacer.bitbucket.org/)
* Set the following global variable: 
```
export LUSTREC=[PATH_TO_LUSTREC_BIN]
export PYTHONPATH=$PYTHONPATH:[PATH_TO_SPACER_PYTHON_BUILD]
```


### How to use Zustre? ###
* To simply verify Lustre code:
```
> python src/zustre.py [LUSTRE_FILE] --node [OBSERVER NODE (default: top)]
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

# Zustre #

Zustre is a modular SMT-based PDR-style verification engine for Lustre programs. It is also an engine to generate assume-guarantee style contract.


### Dependencies ###

* [LustreC (Lustre compiler)](https://bitbucket.org/lememta/lustrec)
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
> python src/zustre.py [LUSTRE_FILE] --node [MAIN LUSTRE NODE (default: top)]
```

* To generate CoCoSpec contract of Lustre code:
```
> python src/zustre.py [LUSTRE_FILE] --cg --node [MAIN LUSTRE NODE (default: top)]
```

### Contact ###
* Temesghen Kahsai (NASA Ames / CMU)
* Arie Gurfinkel (SEI / CMU)

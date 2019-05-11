# Rainfall Semantic Interpreter

This repository contains a semantic interpreter for the Rainfall smart contract language, described in the paper "Smart Contracts as Authorized Production Rules". The paper itself is available at [https://github.com/rainfall-lang/rainfall-paper](https://github.com/rainfall-lang/rainfall-paper).

To build the interpreter you'll need a recent version of GHC (Glasgow Haskell Compiler) installed. Then, in the root of the directory do:

```
$ cabal update
$ cabal install
$ rainfall demo/01-Transfer.rain
```

* More examples are available in 
 [rainfall-lang/rainfall-model/demo](https://github.com/rainfall-lang/rainfall-model/tree/master/demo)

* Proof scripts for the theorems described in the paper are at 
 [rainfall-lang/rainfall-model/proof](https://github.com/rainfall-lang/rainfall-model/tree/master/proof)
 
* A VSCode plugin that provides syntax highligting is at
 [rainfall-lang/rainfall-vscode](https://github.com/rainfall-lang/rainfall-vscode)

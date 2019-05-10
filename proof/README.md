# Rainfall proofs

This directory contains the formalisation and proofs of Rainfall, mechanised in Isabelle/HOL.

The formalisation is laid out as follows:

* Base.thy:
  the definitions of values and facts, along with other prerequisite data type definitions.
* Exp.thy:
  the definition of ASTs for rainfall rules.
  This file corresponds to Figure 4 of the paper (Core Language Grammar).
* Dynamic.thy:
  the dynamic semantics of rainfall rules.
  This file corresponds to Figure 7 of the paper (Dynamic Semantics).
* DynamicLemmas.thy:
  proofs about the dynamic semantics of rainfall rules.
  This file corresponds to Subsection 4.4.1 of the paper.
* Market.thy:
  the market example encoded in rainfall, with proofs that the rules preserve the invariants.
  This file corresponds to Appendix A of the paper.
* Examples.thy:
  sanity-tests for evaluation, to ensure that the formalisation matches our intuition of how the dynamic semantics should behave.
  
## Building the proofs
These proofs were developed with Isabelle 2018.

The proofs build in a few minutes.  To build the proofs, use:
```
isabelle build -d . -v Rainfall
```

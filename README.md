# HOL4 Mechanization of a Martelli-Montanari Unification Algorithm

## Source Paper
["Unification in Linear Time and Space: A Structured Presentation" (1976) by Alberto Martelli and Ugo Montanari](http://puma.isti.cnr.it/publichtml/section_cnr_iei/cnr_iei_1976-B4-041.html "PDF from puma.isti.cnr.it")

## Script files (i.e. HOL sources)
The HOL4 script files are in the hol directory, and are organized as follows:

* Section 2 (term reduction, variable elimination, solved form)
    * term: "t = v | f t1 ... tn" terms.
    * substitution: "var |-> term" substitutions.
    * equation: "t1 = t2" equations and sets thereof; substitutions to solve them.
    * algorithm\_a: simple (non-deterministic) algorithm to solve a set of equations.
* Triangular substitutions (not in paper, but useful for some termination proofs)
    * triangular\_substitution
    * walk
    * walkstar
    * collapse
* Section 3 (multiequations, common part/frontier, refined abstract algorithm)
    * multiequation: MM's famous "set of vars = bag of terms" equation type.
    * multiequation\_system: sets of the above, and operations  on them.
    * algorithm\_b: semi-straightforward algorithm to solve a system
    * unify: improved (still non-deterministic) algorithm using partial order on variables
* Section 4 (memory model, monadic translation of Pascal code)
    * option\_guard: Haskell-style guard for the option monad (eventually to move to HOL)
    * state\_option: state monad transformer applied to the option monad
    * ptypes\_definitions: model of imperative code for dealing with pointer-based list data structures
    * ptypes: properties of the basic imperative code
    * reach: reachability memory cells
    * reduce: imperative implementation of calculating the common part/frontier of a multiequation

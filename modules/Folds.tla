Write a module that implements fold operations for sets, functions, and sequences.

MapThenFoldSet combines mapping and folding operations on sets. 
It applies a transformation function to each element, then reduces the results using a binary operator starting from a base value. 
The choose function determines the order of element selection, which matters for non-associative operations.

------------------------------- MODULE Folds -------------------------------

MapThenFoldSet(op(_,_), base, f(_), choose(_), S) ==
(******************************************************************************)
(* Starting from base, apply op to f(x), for all x \in S, by choosing the set *)
(* elements with `choose`. If there are multiple ways for choosing an element,*)
(* op should be associative and commutative. Otherwise, the result may depend *)
(* on the concrete implementation of `choose`.                                *)
(*                                                                            *)
(* FoldSet, a simpler version for sets is contained in FiniteSetsEx.          *)
(* FoldFunction, a simpler version for functions is contained in Functions.   *)
(* FoldSequence, a simpler version for sequences is contained in SequencesExt.*)
(*                                                                            *)
(* Example:                                                                   *)
(*                                                                            *)
(*  MapThenFoldSet(LAMBDA x,y: x \cup y,                                      *)
(*                 {},                                                        *)
(*                 LAMBDA x: {{x}},                                           *)
(*                 LAMBDA set: CHOOSE x \in set: TRUE,                        *)
(*                 {1,2})                                                     *)
(*       = {{1},{2}}                                                          *)
(******************************************************************************)
  LET iter[s \in SUBSET S] ==
        IF s = {} THEN base
        ELSE LET x == choose(s)
             IN  op(f(x), iter[s \ {x}])
  IN  iter[S]


=============================================================================

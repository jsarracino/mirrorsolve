Inductive smt_sorts := 
  | SInt : unit -> smt_sorts
  | SBool
  | SBitVector.

Register SInt as p4a.core.smt_int.
Register SBool as p4a.core.smt_bool.
Register SBitVector as p4a.core.smt_bv.  

Inductive smt_theory := | MkTheory : smt_sorts -> smt_theory.

Register MkTheory as p4a.core.mk_theory.

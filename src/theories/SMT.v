Require Import Coq.Strings.String.

Inductive smt_sort := 
  | SInt : unit -> smt_sort
  | SBool : unit -> smt_sort
  | SBitVector : unit -> smt_sort.

Register SInt as p4a.core.smt_int.
Register SBool as p4a.core.smt_bool.
Register SBitVector as p4a.core.smt_bv.  

Inductive smt_fun := 
  | F_sym : string -> smt_fun
  | BoolLit : unit -> smt_fun
  | IntLit : unit -> smt_fun.

Register F_sym as p4a.core.fun_sym.
Register BoolLit as p4a.core.bool_lit.
Register IntLit as p4a.core.int_lit.

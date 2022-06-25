Require Import Coq.Strings.String.

Inductive smt_sort := 
  | SInt : unit -> smt_sort
  | SBool : unit -> smt_sort
  | SBitVector : unit -> smt_sort
  | SCustom : string -> smt_sort.

Register SInt as ms.core.smt_int.
Register SBool as ms.core.smt_bool.
Register SBitVector as ms.core.smt_bv.  
Register SCustom as ms.core.smt_custom.  

Inductive smt_ind_base := 
  | SIRec 
  | SISort : smt_sort -> smt_ind_base.

Inductive smt_ind := 
  | SICases : list (string * list smt_ind_base) -> smt_ind.

Register SIRec as ms.core.smt_ind_rec.
Register SISort as ms.core.smt_ind_sort.
Register SICases as ms.core.smt_ind_cases.  

Inductive smt_fun := 
  | F_sym : string -> smt_fun
  | BoolLit : unit -> smt_fun
  | IntLit : unit -> smt_fun 
  | BVLit : unit -> smt_fun.

Register F_sym as ms.core.fun_sym.
Register BoolLit as ms.core.bool_lit.
Register IntLit as ms.core.int_lit.
Register BVLit as ms.core.bv_lit.

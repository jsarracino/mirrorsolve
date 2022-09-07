Require Import Coq.Strings.String.

Inductive smt_sort_base := 
  | SInt | SBool | SBitVector
  | SCustom : string -> smt_sort_base.

Register SInt as ms.core.smt_int.
Register SBool as ms.core.smt_bool.
Register SBitVector as ms.core.smt_bv.  
Register SCustom as ms.core.smt_custom.  

Inductive smt_ind_base := 
  | SIRec 
  | SISort : smt_sort_base -> smt_ind_base.

Inductive smt_ind := 
  | SICases : list (string * list smt_ind_base) -> smt_ind.

Inductive smt_sort := 
  | SortBase : smt_sort_base -> smt_sort 
  | SortInd : string -> smt_ind -> smt_sort.

Register SIRec as ms.core.smt_ind_rec.
Register SISort as ms.core.smt_ind_sort.
Register SICases as ms.core.smt_ind_cases. 
Register SortBase as ms.core.smt_sort_base.
Register SortInd as ms.core.smt_sort_ind.

Inductive smt_fun_base := 
  | F_sym : string -> smt_fun_base
  | BoolLit : smt_fun_base
  | IntLit : smt_fun_base 
  | BVLit : smt_fun_base.

Register F_sym as ms.core.fun_sym.
Register BoolLit as ms.core.bool_lit.
Register IntLit as ms.core.int_lit.
Register BVLit as ms.core.bv_lit.

Inductive smt_fun := 
  | FPrim : smt_fun_base -> smt_fun 
  | FUninterp : string -> smt_fun.

Register FPrim as ms.core.fprim.
Register FUninterp as ms.core.funinterp.
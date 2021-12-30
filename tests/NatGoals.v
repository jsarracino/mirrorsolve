Require Import MirrorSolve.FirstOrder.

Require Import MirrorSolve.N.
Require Import MirrorSolve.Z.

Require Import MirrorSolve.N2Z.
Require Import MirrorSolve.SMT.

Require Import MirrorSolve.HLists.

Import HListNotations.

Require Import Coq.Strings.String.


Declare ML Module "mirrorsolve".

RegisterSMTSort ZS SInt.
RegisterSMTSort BS SBool.



RegisterSMTFun Z.Plus "+" 2.
RegisterSMTFun Z.Gte ">=" 2.
RegisterSMTBuiltin Z.BLit BoolLit.
RegisterSMTBuiltin Z.ZLit IntLit.

  
Lemma nat_eq_refl : 
  interp_fm (sig := N.sig) (VEmp _ N.fm_model) (FForall (sig :=  N.sig) NS (FForall (sig :=  N.sig) NS (FEq 
    (TFun N.sig N.Plus (
      ((TVar (VHere _ _ _)) ::: (TVar (VThere _ _ _ _ (VHere _ _ _)) ::: hnil))
    ))
    (TFun N.sig N.Plus (
      ((TVar (VHere _ _ _)) ::: (TVar (VThere _ _ _ _ (VHere _ _ _)) ::: hnil))
    ))
  ))).
Proof.
  eapply n2z_corr.
  match goal with 
  | |- interp_fm ?v ?f => 
    set (v' := v);
    set (f' := f)
  end.
  vm_compute in f'.
  
  
  subst v'.

  unfold n2z_func.
  autorewrite with fmap_valu.
  subst f'.

  match goal with 
  | |- ?G => 
    check_interp_pos G; admit
  end.
Admitted.
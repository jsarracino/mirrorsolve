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
RegisterSMTFun Z.Lt "<" 2.
RegisterSMTFun Z.Mul "*" 2.
RegisterSMTBuiltin Z.BLit BoolLit.
RegisterSMTBuiltin Z.ZLit IntLit.

Notation bop o l r := (TFun N.sig o (l ::: r ::: hnil)).
Notation nlit n := (TFun N.sig (N.NLit n) hnil).
Notation tru := (TFun N.sig (N.BLit true) hnil).

  (* forall n m, n <> 0 -> m * m = 2 * n * n -> m < 2 * n
   *)
Lemma nat_square_decreasing : 
  interp_fm (sig := N.sig) (VEmp _ N.fm_model) (FForall (sig :=  N.sig) NS (FForall (sig :=  N.sig) NS (
    FImpl (FNeg _ (FEq 
      (TVar (VThere _ _ _ _ (VHere _ _ _)))
      (nlit 0)
      ))
    (FImpl (FEq 
      (bop N.Mul (TVar (VHere _ _ _)) (TVar ((VHere _ _ _))))
      (bop N.Mul (nlit 2) (bop N.Mul (TVar (VThere _ _ _ _ (VHere _ _ _))) (TVar (VThere _ _ _ _ (VHere _ _ _))))))
    (FEq tru
      (bop N.Lt (TVar (VHere _ _ _)) (bop N.Mul (nlit 2) (TVar (VThere _ _ _ _ (VHere _ _ _)))))
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
Require Import MirrorSolve.FirstOrder.

Require Import MirrorSolve.N.
Require Import MirrorSolve.Z.

Require Import MirrorSolve.N2Z.
Require Import MirrorSolve.SMT.

Require Import MirrorSolve.HLists.
Require Import Coq.Lists.List.

Import HListNotations.
Import ListNotations.

Require Import Coq.Strings.String.

Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.

Notation bop o l r := (TFun N.sig o (l ::: r ::: hnil)).
Notation nlit n := (TFun N.sig (N.NLit n) hnil).
Notation tru := (TFun N.sig (N.BLit true) hnil).
Notation zero := (nlit 0).

MetaCoq Quote Definition c_plus := @plus.

Obligation Tactic := intros.
Equations reflect_t2tm {c: ctx N.sig} (t: term) (r_args: list (option ({srt & N.tm c srt}))) : option ({srt & N.tm c srt}) := 
  reflect_t2tm (tApp f _) r_args := 
  if eq_term f c_plus then
    match r_args with 
    | [Some l; Some r] => 
      let (sl, tl) := l in
      let (sr, tr) := r in 
      match sl as sl' return (N.tm c sl' -> N.tm c sr -> option ({srt & N.tm c srt})) with
      | NS => 
        match sr as sr' return (N.tm c NS -> N.tm c sr' -> option ({srt & N.tm c srt})) with
        | NS => fun tl' tr' => Some (existT _ _ (TFun N.sig N.Plus (tl' ::: tr' ::: hnil)))
        | _ => fun _ _ => None
        end
      | _ => fun _ _ => None
      end tl tr
    | _ => None
    end
  else 
    None;
  reflect_t2tm _ _ := None.

MetaCoq Quote Definition nat_ind := (nat).
MetaCoq Quote Definition bool_ind := (bool).

Definition get_ind (t: term) : option inductive := 
  match t with 
  | tInd x _ => Some x
  | _ => None
  end.

Definition nat_ind' : inductive.
  set (foo := get_ind nat_ind).
  compute in foo.
  match goal with 
  | _ := Some ?X |- _ => exact X
  end.
Defined.
Definition bool_ind' : inductive.
  set (foo := get_ind bool_ind).
  compute in foo.
  match goal with 
  | _ := Some ?X |- _ => exact X
  end.
Defined.

Definition ind2srt (i: inductive) : option N.sorts := 
  if eq_inductive i nat_ind' then Some N.NS
  else if eq_inductive i bool_ind' then Some N.BS
  else None.

MetaCoq Quote Definition test := (forall (n: nat), n = n).
Eval vm_compute in reflect_t2fm N.sig (@reflect_t2tm) ind2srt N.sorts_eq_dec (CEmp _) test.

Declare ML Module "mirrorsolve".

RegisterSMTSort ZS SInt.
RegisterSMTSort BS SBool.

RegisterSMTFun Z.Plus "+" 2.
RegisterSMTFun Z.Gte ">=" 2.
RegisterSMTFun Z.Lt "<" 2.
RegisterSMTFun Z.Mul "*" 2.

RegisterSMTBuiltin Z.BLit BoolLit.
RegisterSMTBuiltin Z.ZLit IntLit.

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


Require Import Coq.Arith.PeanoNat.

Require Import FunInd.
Fixpoint pow base exp := 
  match exp with 
  | 0 => 1
  | S exp' => base * pow base exp'
  end.

Fixpoint my_append (l: list nat) (r: list nat) := 
  match l with 
  | nil => r
  | cons x l' => 
    cons x (my_append l' r)
  end.

From Hammer Require Import Hammer.

Variable (pow_uninterp: nat -> nat -> nat).

Variable (pow_uninterp_corr: forall n m, pow_uninterp n m = pow n m).

Fixpoint ple_eval (m: nat) (n: nat) : Prop := 
  match n with 
  | 0 => pow_uninterp m 0 = 1
  | S n' => pow_uninterp m (S n') = m * pow_uninterp m n' /\ ple_eval m n'
  end.

Lemma ple_eval_corr : 
  forall m n, 
    ple_eval m n.
Proof.
  induction n.
  - simpl.
    erewrite pow_uninterp_corr.
    trivial.
  - simpl.
    split; trivial.
    repeat erewrite pow_uninterp_corr.
    trivial.
Qed.

Lemma pow_1_7: 
  pow 1 7 = 1.
Proof.
  erewrite <- pow_uninterp_corr.
  assert (ple_eval 1 7) by eapply ple_eval_corr.
  unfold ple_eval in H.
Abort.

Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.
Import HListNotations.
Require Import MirrorSolve.SMT.
Require Import MirrorSolve.BV.

Local Declare ML Module "mirrorsolve".

Require Import MirrorSolve.Z.
Require Import MirrorSolve.N2Z.

RegisterSMTSort ZS SInt.
RegisterSMTSort BS SBool.

RegisterSMTUF "power" ZS ZS BS.

RegisterSMTBuiltin Z.ZLit IntLit.

Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.
Require Import MirrorSolve.Reflection.Tactics.

Definition is_z_term (t: term) : bool := 
  match t with 
  | tApp c _ => 
    orb (eq_term c c_zpos) (eq_term c c_zneg)
  | _ => eq_term t c_zzero
  end.

Require Import Coq.ZArith.BinIntDef.

Require Import Coq.Lists.List.

Notation zlit := (tacLit sig fm_model z_lit).

Definition match_tacs : list ((term -> bool) * tac_syn sig fm_model) := [
   (is_z_term, 
    zlit 
      (fun z => existT _ ZS z) 
      (fun z _ => existT _ ZS (TFun sig (ZLit z) hnil)))
  ].

MetaCoq Quote Definition z_ind := (Z).

Definition match_inds : list (term * sorts) := [
    (z_ind, ZS)
  ].

MetaCoq Quote Definition test_1 := (1 = 1)%Z.
  
Goal (1 = 1)%Z.
Proof.
  reflect_goal Z.sig Z.fm_model Z.sorts_eq_dec match_tacs match_inds test_1.
  match goal with 
  | |- ?G => check_interp_pos G
  end.
Admitted.

(* TODO: 
  1) develop metaprogramming plumbing for reflecting pow as an uninterpreted fun symbol, and 
  2) recognize uninterpreted function symbols in the backend
*)
Lemma pow_gt_lin_r : forall p, pow 1 p = 1.
Proof.
  intros.
  (* induction p *)

  (* demo 1: manual symbolic logical evaluation *)

  assert (pow 1 p = pow 1 p) by trivial.
  revert H.
  revert p.
  induction p.

  - intros. 
    simpl in *. 
    trivial.
  - intros.
    simpl pow at 1 in H.
    erewrite <- H.
    erewrite Nat.add_0_r.
    eapply IHp.
    trivial.

  (* demo 2: symbolic logical evaluation with functional induction  *)

  (* functional induction (pow 1 p) using pow_ind.

  - intros; trivial. 
  - erewrite IHn0.
    trivial. *)
Qed.

From Hammer Require Import Hammer.

Ltac try_ind base_tac := 
  multimatch goal with 
  | |- forall (X: _), _ => 
    intros X; try_ind base_tac
  | |- ?X -> _ => 
    intros X; try_ind base_tac
  | |- forall (X: _), _ => 
    induction X; try_ind base_tac
  | |- ?X -> _ => 
    induction X; try_ind base_tac
  | _ => base_tac
  end.

Set Hammer ATPLimit 3.



Lemma pow_eq_zero: 
  forall a b, pow a b = 0 -> a = 0.
Proof. 
  try_ind hammer.
  induction b; hammer.
  intros.
  sauto.
  hammer.
  induction b.
  - intros; inversion H.
  - intros.
    simpl in *.
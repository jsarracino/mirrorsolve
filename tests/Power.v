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

Require Import MirrorSolve.N.
Require Import MirrorSolve.Z.
Require Import MirrorSolve.N2Z.


RegisterSMTSort ZS SInt.
(* RegisterSMTSort BS SBool. *)
RegisterCustomSort BS "BS".

RegisterSMTUF "pow" ZS ZS BS.

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

Definition is_nat_term (t: term) : bool := 
  match t with 
  | tApp f _ => 
    eq_term f c_nsucc
  | _ => eq_term t c_nzero
  end.

Require Import Coq.ZArith.BinIntDef.

Require Import Coq.Lists.List.

Require Import Coq.Strings.String.
Require Import MirrorSolve.UF.
Import ListNotations.

Notation sig := (N.sig).

Definition symbs : list (string * list (sig_sorts sig) * sig_sorts sig) := ([
  ("pow", [NS; NS], NS)
]%string).

Lemma symbs_contents : 
  forall s args r, 
    In (s, args, r) symbs <-> 
    s = "pow"%string /\ args = [NS; NS] /\ r = NS.
Proof.
  intros.
  unfold symbs.
  split; intros.
  - inversion H; subst.
    + inversion H0; subst.
      repeat econstructor.
    + inversion H0.
  - destruct H as [? [? ?]]; subst.
    left; econstructor.
Defined.

Definition interp_syms (sym: string) (a: list (sig_sorts sig)) (r: sig_sorts sig) : 
  In (sym, a, r) symbs -> HList.t (FirstOrder.mod_sorts sig N.fm_model) a -> FirstOrder.mod_sorts sig N.fm_model r.
  intros.
  pose proof symbs_contents sym a r.
  destruct H0.
  specialize (H0 H).
  destruct H0 as [? [? ?]].
  subst.
  inversion X; subst.
  inversion X1; subst.
  simpl in *.
  exact (pow X0 X2).
Defined.

Notation sig' := (UF.sig sig symbs).
Definition uf_model := UF.fm_model sig N.fm_model symbs interp_syms.

Lemma in_pow : 
  In ("pow", [NS; NS], NS)%string symbs.
Proof.
  simpl.
  left; trivial.
Defined.

Notation natlit := (tacLit sig' uf_model nat_lit).
MetaCoq Quote Definition t_pow := (pow).

Definition is_pow := eq_term t_pow.

Program Definition match_tacs : list ((term -> bool) * tac_syn sig' uf_model) := [
  ( is_pow, tacFun _ _ {| deep_f := UFun sig symbs in_pow |} ); 
  ( is_nat_term, 
    natlit 
      (fun z => existT _ NS z) 
      (fun z _ => existT _ NS (TFun _ (CFun _ symbs (NLit z)) hnil)))
  ].

MetaCoq Quote Definition n_ind := (nat).

Definition match_inds : list (term * N.sorts) := [
    (n_ind, NS)
  ].

MetaCoq Quote Definition test_1 := (pow 1 2 = 1).

Ltac simpl_denote_tm :=
  match goal with 
  | |- denote_t2fm _ _ _ _ _ _ _ _ = Some _ => 
    let x := fresh "x" in 
    set (x := denote_t2fm _ _ _ _ _ _ _ _);
    
    simpl in x;
    unfold eq_rect_r in x;
    simpl in x; 
    exact eq_refl
  end.

Ltac reflect_goal sig model srts_eq_dec mtacs minds t' := 
  match goal with 
  | |- ?G => 
    eapply denote_extract_specialized with (s := sig) (m := model) (sorts_eq_dec := srts_eq_dec) (match_tacs := mtacs) (match_inds := minds) (p' := G) (t := t')
  end; [
    simpl_denote_tm |
    simpl_extract_tm |
    discharge_equiv_denote_orig; autorewrite with mod_fns; eauto | 
    let v' := fresh "v" in 
    let f' := fresh "f" in 
    match goal with 
    | |- interp_fm ?v ?f => 
      set (v' := v);
      set (f' := f)
    end;
    vm_compute in f';
    subst v';
    subst f'
  ]. 
  
Goal (pow 1 2 = 1).
Proof.
  reflect_goal (UF.sig sig symbs) uf_model N.sorts_eq_dec match_tacs match_inds test_1.

  simpl.
  unfold eq_rect_r.
  simpl eq_rect.
  2: {
    autorewrite with interp_fm.
    autorewrite with interp_tm.
    simpl.
    vm_compute.
  }
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
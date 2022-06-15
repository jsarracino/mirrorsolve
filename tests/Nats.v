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


MetaCoq Quote Definition c_plus := @plus.
MetaCoq Quote Definition c_times := @Nat.mul.
MetaCoq Quote Definition c_lt := @Nat.ltb.

Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.
Require Import MirrorSolve.Reflection.Tactics.

Notation natlit := (tacLit N.sig N.fm_model nat_lit).
Notation boollit := (tacLit N.sig N.fm_model bool_lit).

Program Definition match_tacs : list ((term -> bool) * tac_syn N.sig N.fm_model) := [
    ( eq_term c_plus, tacFun _ _ {| deep_f := N.Plus |} )
  ; ( eq_term c_times, tacFun _ _ {| deep_f := N.Mul |} )
  ; ( eq_term c_lt, tacFun _ _ {| deep_f := N.Lt |} )
  ; ( is_nat_term, 
    natlit 
      (fun z => existT _ NS z) 
      (fun z _ => existT _ NS (TFun _ (NLit z) hnil)))
  ; ( is_bool_term, 
    boollit 
      (fun b => existT _ N.BS b) 
      (fun b _ => existT _ N.BS (TFun _ (N.BLit b) hnil)))
  ].

MetaCoq Quote Definition nat_ind := (nat).
MetaCoq Quote Definition bool_ind := (bool).

Definition match_inds : list (term * N.sorts) := [
    (nat_ind, NS)
  ; (bool_ind, N.BS)
  ].

Program Definition mt_wf: match_tacs_wf N.sig N.fm_model N.sorts_eq_dec match_tacs := {| 
  match_tacs_sound_some := _;
  match_tacs_sound_none := _;
|}.
Admit Obligations.

Require Import MirrorSolve.SMT.
Require Import MirrorSolve.BV.

Local Declare ML Module "mirrorsolve".

RegisterSMTSort ZS SInt.

RegisterSMTFun Z.Plus "+" 2.
RegisterSMTFun Z.Lt "<" 2.
RegisterSMTFun Z.Mul "*" 2.

RegisterSMTBuiltin Z.ZLit IntLit.
RegisterSMTBuiltin Z.BLit BoolLit.

Require Import MirrorSolve.Axioms.
Import UnsoundAxioms.

Ltac check_goal := 
  match goal with 
  | |- ?G => check_interp_pos G; eapply UnsoundAxioms.interp_true
  end.

(* pulled from Coqhammer's benchmarks on the irrationality of sqrt(2) *)
MetaCoq Quote Definition hard_goal := 
  (forall n m, n <> 0 -> m * m = 2 * n * n -> Nat.ltb m (2 * n) = true).
  
Goal (forall n m, n <> 0 -> m * m = 2 * n * n -> Nat.ltb m (2 * n) = true).
Proof.
  reflect_goal N.sig N.fm_model N.sorts_eq_dec match_tacs match_inds mt_wf hard_goal.
  
  (* fmap N -> Z *)
  eapply n2z_corr.
  match goal with 
  | |- interp_fm ?V ?FM => 
    set (v := V);
    set (f := FM);
    vm_compute in v;
    vm_compute in f;
    subst v;
    subst f
  end.
  (* actually discharge the query, and use an axiom to close the proof *)
  check_goal.
Qed.

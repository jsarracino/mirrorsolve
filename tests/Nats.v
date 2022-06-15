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

MetaCoq Quote Definition c_plus := @plus.
MetaCoq Quote Definition c_times := @Nat.mul.
MetaCoq Quote Definition c_sub := @Nat.sub.
MetaCoq Quote Definition c_div := @Nat.div.
MetaCoq Quote Definition c_mod := @Nat.modulo.
MetaCoq Quote Definition c_lte := @Nat.leb.
MetaCoq Quote Definition c_lt := @Nat.ltb.

MetaCoq Quote Definition c_tru := true.
MetaCoq Quote Definition c_fls := false.
MetaCoq Quote Definition c_zero := 0.
MetaCoq Quote Definition c_succ := S.

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

(* This is an analogous match but for reflecting Coq types into FOL sorts. *)
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
RegisterSMTFun Z.Gte ">=" 2.
RegisterSMTFun Z.Lt "<" 2.
RegisterSMTFun Z.Mul "*" 2.
RegisterSMTFun Z.Lte "<=" 2.

RegisterSMTBuiltin Z.ZLit IntLit.
RegisterSMTBuiltin Z.BLit BoolLit.

Require Import MirrorSolve.Axioms.
Import UnsoundAxioms.


(* pulled from Coqhammer's benchmarks on the irrationality of sqrt(2) *)
MetaCoq Quote Definition hard_goal := 
  (forall n m, n <> 0 -> m * m = 2 * n * n -> Nat.ltb m (2 * n) = true).
  
Goal (forall n m, n <> 0 -> m * m = 2 * n * n -> Nat.ltb m (2 * n) = true).
Proof.
  pose proof @denote_extract_specialized N.sig N.fm_model N.sorts_eq_dec match_tacs match_inds mt_wf (reindex_vars hard_goal).
  evar (fm: FirstOrder.fm N.sig (SLNil (sig_sorts N.sig))).
  specialize (H fm).
  assert (extract_t2fm N.sig
  (fun c : ctx N.sig =>
   extract_t2tm N.sig N.fm_model N.sorts_eq_dec match_tacs)
  (i2srt N.sig match_inds) N.sorts_eq_dec (SLNil (sig_sorts N.sig))
  (reindex_vars hard_goal) = Some fm) by (exact eq_refl).

  match goal with 
  | |- ?G => 
    assert (denote_t2fm N.sig N.fm_model N.sorts_eq_dec
    (denote_tm N.sig N.fm_model N.sorts_eq_dec match_tacs)
    (i2srt N.sig match_inds) (VEmp N.sig N.fm_model)
    (reindex_vars hard_goal) = G) by (exact eq_refl)
  end.

  erewrite H1 in *.
  eapply H; eauto.
  vm_compute in fm; subst fm.

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
  match goal with 
  | |- ?G => check_interp_pos G; eapply interp_true
  end.
Qed.

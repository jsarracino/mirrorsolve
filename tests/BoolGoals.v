Require Import MirrorSolve.FirstOrder.

Require Import MirrorSolve.Bool.
Require Import MirrorSolve.SMT.

Require Import MirrorSolve.HLists.
Require Import Coq.Lists.List.

Import HListNotations.
Import ListNotations.

Require Import Coq.Strings.String.

Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.

Require Import Coq.Bool.Bool.

Require Import MirrorSolve.Reflection.Tactics.

MetaCoq Quote Definition c_and := andb.
MetaCoq Quote Definition c_or := orb.
MetaCoq Quote Definition c_neg := negb.
MetaCoq Quote Definition c_impl := implb. 

MetaCoq Quote Definition c_tru := true.
MetaCoq Quote Definition c_fls := false.

Notation bfun := (@tacFun sig _).
Notation blit := (@tacLit sig fm_model).


Program Definition match_tacs : list (term * tac_syn sig fm_model) := [
      (c_and, bfun {| deep_f := BAnd |})
    ; (c_or,  bfun {| deep_f := BOr |})
    ; (c_impl, bfun {| deep_f := BImpl |})
    ; (c_neg, bfun {| deep_f := BNot |})
    ; (c_tru, blit BoolSort true (fun _ => TFun _ (BLit true) hnil))
    ; (c_fls, blit BoolSort false (fun _ => TFun _ (BLit false) hnil))
  ]. 
MetaCoq Quote Definition bool_ind := (bool).

Definition match_inds : list (term * sorts) := [
    (bool_ind, BoolSort)
  ].

(* configure backend *)

Declare ML Module "mirrorsolve".

RegisterSMTSort BoolSort SBool.

RegisterSMTFun BAnd "and" 2.
RegisterSMTFun BOr "or" 2.
RegisterSMTFun BNot "not" 1.
RegisterSMTFun BImpl "=>" 2.

RegisterSMTBuiltin BLit BoolLit.

Require Import MirrorSolve.Axioms.

Import UnsoundAxioms.

  (* taken from smtcoq's examples *)
MetaCoq Quote Definition test := (forall a b c, 
  (a || b || c) && 
  ((negb a) || (negb b) || (negb c)) && 
  ((negb a) || b) && 
  ((negb b) || c) && 
  ((negb c) || a) = false).

Goal (forall a b c,
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false).
Proof.
  Transparent denote_tm.
  reflect_goal sig fm_model sorts_eq_dec match_tacs match_inds test.
  match goal with 
  | |- ?G => 
    check_interp_pos G; eapply interp_true
  end.
Qed.

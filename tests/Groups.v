
Require Import MirrorSolve.SMT.
Require Import MirrorSolve.BV.

(* pulled from: https://people.cs.umass.edu/~arjun/courses/cs691pl-spring2014/assignments/groups.html *)

(* The set of the group. *)
(*** MS BEGIN {"type": "definition"} *)
Parameter G : Set.
(*** MS END {"type": "definition"} *)

(* The binary operator. *)
(*** MS BEGIN {"type": "definition"} *)
Parameter f : G -> G -> G.
(*** MS END {"type": "definition"} *)

(* The group identity. *)
(*** MS BEGIN {"type": "definition"} *)
Parameter e : G.
(*** MS END {"type": "definition"} *)

(* The inverse operator. *)
(*** MS BEGIN {"type": "definition"} *)
Parameter i : G -> G.
(*** MS END {"type": "definition"} *)

(* For readability, we use infix <+> to stand for the binary operator. *)
Infix "<+>" := f (at level 50, left associativity).

(* The operator [f] is associative. *)
(*** MS BEGIN {"type": "definition"} *)
Axiom assoc : forall a b c, a <+> b <+> c = a <+> (b <+> c).
(*** MS END {"type": "definition"} *)

(* [e] is the right-identity for all elements [a] *)
(*** MS BEGIN {"type": "definition"} *)
Axiom id_r : forall a, a <+> e = a.
(*** MS END {"type": "definition"} *)

(* [i a] is the right-inverse of [a]. *)
(*** MS BEGIN {"type": "definition"} *)
Axiom inv_r : forall a, a <+> i a = e.
(*** MS END {"type": "definition"} *)

(* encoding groups in in FOL *)

Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.Groups.

Require Import MirrorSolve.HLists.

Require Import MirrorSolve.UF.

Require Import Coq.Strings.String.

Require Import Coq.Lists.List.

Import ListNotations.

Set Universe Polymorphism.

Notation sig := Groups.sig.

Definition group_model := Groups.fm_model G e f i.

Require Import MirrorSolve.HLists.

Import HListNotations.

Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.
Require Import MirrorSolve.Reflection.Tactics.

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition t_f := f.
MetaCoq Quote Definition t_i := i.
MetaCoq Quote Definition t_e := e.
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(* Some match tactics for the meta-interpreter. 
   The meta-interpreter converts these definitions into a reflection procedure between pure Coq goals and FOL terms in the UF + Groups combined theory. 
*)

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
Notation uf op := (tacFun _ _ (Mk_fun_sym sig _ _ op)).

Definition match_tacs : list ((term -> bool) * tac_syn sig group_model) := [
    ( eq_term t_f, uf f_f)
  ; ( eq_term t_i, uf i_f )
  ; ( eq_term t_e, uf e_f)
  ].

MetaCoq Quote Definition g_ind := (G).

(* This is an analogous match but for reflecting Coq types into FOL sorts. *)
Definition match_inds : list ((term -> bool) * Groups.sorts) := [
    (eq_term g_ind, G')
  ].
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(* Next we configure the backend solver. We need to tell the OCaml backend about: 
   A custom sort symbol for the Groups.G' sort;
   and custom UF symbols for e, op, and inv. 

   The syntax for a UF declaration is 
    RegisterSMTUF <symbol name as a string> <return sort> <list of argument sorts>
*)
(*** MS BEGIN {"type": "configuration", "config_type":"plugin"} *)
Local Declare ML Module "mirrorsolve".
RegisterCustomSort Groups.G' "G".
RegisterSMTUF "e" G'.
RegisterSMTUF "f" G' G' G'.
RegisterSMTUF "i" G' G'.

RegisterSMTFun Groups.e_f "e" 0.
RegisterSMTFun Groups.f_f "f" 2.
RegisterSMTFun Groups.i_f "i" 1.
(*** MS END {"type": "configuration", "config_type":"plugin"} *)

Transparent denote_tm.

Require Import MirrorSolve.Axioms. (* trust the SMT solver in a typesafe way *)

(*** MS BEGIN {"type": "configuration", "config_type":"tactics"} *)
Ltac prep_proof := Utils.pose_all (tt, assoc, inv_r, id_r);
  Utils.revert_all.

Ltac extend_ctx H f := pose proof H;
  f.

Ltac reflect t := reflect_goal sig group_model sorts_eq_dec match_tacs match_inds t.
 

Ltac check_goal := 
  match goal with 
  | |- ?G => check_unsat_neg G; eapply UnsoundAxioms.interp_true
  end.

SetSMTSolver "z3".
(*** MS END {"type": "configuration", "config_type":"tactics"} *)

(* Some group theory results translated into Coq *)

From Hammer Require Import Hammer.

Set Hammer ATPLimit 5.
Set Hammer ReconstrLimit 10.

MetaCoq Quote Definition unique_id_term := (
  (forall a : G, a <+> e = a) ->
(forall a : G, a <+> i a = e) ->
(forall a b c : G, a <+> b <+> c = a <+> (b <+> c)) ->
forall a : G, a <+> a = a -> a = e
).

(*** MS BEGIN {"type": "proof_definition"} *)
Lemma unique_id : 
  forall a, 
    a <+> a = a -> 
    a = e.
(*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  intros.
  assert (a <+> i a = a <+> i a) by trivial.
  erewrite <- H in H0 at 1.
  erewrite assoc in H0.
  erewrite inv_r in H0.
  erewrite id_r in H0.
  auto.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  prep_proof;
  hammer.
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
  prep_proof;
  reflect unique_id_term;
  check_goal.
  (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
Qed.

(*** MS BEGIN {"type": "configuration", "config_type":"tactics"} *)
Ltac prep_proof' := extend_ctx unique_id prep_proof.
(*** MS END {"type": "configuration", "config_type":"tactics"} *)

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition inv_l_term := (
  (forall a : G, a <+> a = a -> a = e) ->
  (forall a : G, a <+> e = a) ->
  (forall a : G, a <+> i a = e) ->
  (forall a b c : G, a <+> b <+> c = a <+> (b <+> c)) ->
  forall a : G, i a <+> a = e
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(* [i a] is the left-inverse of [a]. *)
(*** MS BEGIN {"type": "proof_definition"} *)
Lemma inv_l : 
  forall a, 
    i a <+> a = e.
(*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  intros.
  eapply unique_id.
  erewrite <- assoc.
  erewrite assoc with (a := i a).
  erewrite inv_r.
  erewrite id_r.
  trivial.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  prep_proof';
  hammer.
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
  prep_proof';
  reflect inv_l_term;
  check_goal.
  (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
Qed.


(*** MS BEGIN {"type": "configuration", "config_type":"tactics"} *)
Ltac prep_proof'' := extend_ctx inv_l prep_proof'.
(*** MS END {"type": "configuration", "config_type":"tactics"} *)

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition id_l_term := (
  (forall a : G, i a <+> a = e) ->
  (forall a : G, a <+> a = a -> a = e) ->
  (forall a : G, a <+> e = a) ->
  (forall a : G, a <+> i a = e) ->
  (forall a b c : G, a <+> b <+> c = a <+> (b <+> c)) ->
  forall a : G, e <+> a = a
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(* [e] is the left-identity. *)
(*** MS BEGIN {"type": "proof_definition"} *)
Lemma id_l : 
  forall a, 
    e <+> a = a.
    (*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  intros.
  erewrite <- inv_r with (a := a).
  erewrite assoc.
  erewrite inv_l.
  erewrite id_r.
  trivial.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  prep_proof'';
  hammer.
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
  prep_proof'';
  reflect id_l_term;
  check_goal.
  (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
Qed.


(*** MS BEGIN {"type": "configuration", "config_type":"tactics"} *)
Ltac prep_proof_0 := extend_ctx id_l prep_proof''.
(*** MS END {"type": "configuration", "config_type":"tactics"} *)

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition cancel_r_term := (
  (forall a : G, e <+> a = a) ->
  (forall a : G, i a <+> a = e) ->
  (forall a : G, a <+> a = a -> a = e) ->
  (forall a : G, a <+> e = a) ->
  (forall a : G, a <+> i a = e) ->
  (forall a b c : G, a <+> b <+> c = a <+> (b <+> c)) ->
  forall a b x : G, a <+> x = b <+> x -> a = b
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)


(* [x] can be cancelled on the right. *)
(*** MS BEGIN {"type": "proof_definition"} *)
Lemma cancel_r : 
  forall a b x, 
    a <+> x = b <+> x -> 
    a = b.
    (*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  intros.
  assert (a <+> x <+> i x = a <+> x <+> i x) by trivial.
  erewrite H in H0 at 1.
  repeat erewrite assoc in H0.
  repeat erewrite inv_r in H0.
  repeat erewrite id_r in H0.
  auto.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":1, "finished":0} *)
  (*
  prep_proof_0;
  hammer. *)
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":1, "finished":0} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":0} *)
  (* prep_proof_0;
  reflect cancel_r_term;
  check_goal. *)
  (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":0} *)
Admitted.

(*** MS BEGIN {"type": "configuration", "config_type":"tactics"} *)
Ltac prep_proof_1 := extend_ctx cancel_r prep_proof_0.
(*** MS END {"type": "configuration", "config_type":"tactics"} *)

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition cancel_l_term := (
  (forall a b x : G, a <+> x = b <+> x -> a = b) ->
  (forall a : G, e <+> a = a) ->
  (forall a : G, i a <+> a = e) ->
  (forall a : G, a <+> a = a -> a = e) ->
  (forall a : G, a <+> e = a) ->
  (forall a : G, a <+> i a = e) ->
  (forall a b c : G, a <+> b <+> c = a <+> (b <+> c)) ->
  forall a b x : G, x <+> a = x <+> b -> a = b
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(* [x] can be cancelled on the left. *)
(*** MS BEGIN {"type": "proof_definition"} *)
Lemma cancel_l: 
  forall a b x, 
    x <+> a = x <+> b -> 
    a = b.
  (*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  intros.
  assert (i x <+> x <+> a = i x <+> x <+> a) by trivial.
  erewrite assoc in H0.
  erewrite H in H0 at 1.
  repeat erewrite <- assoc in H0.
  erewrite inv_l in H0.
  repeat erewrite id_l in H0.
  auto.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":1, "finished":0} *)
  (* prep_proof_1; 
  hammer. *)
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":1, "finished":0} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":0} *)
  (* prep_proof_1;
  reflect cancel_l_term;
  check_goal. *)
  (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":0} *)
Admitted.


(*** MS BEGIN {"type": "configuration", "config_type":"tactics"} *)
Ltac prep_proof_2 := extend_ctx cancel_l prep_proof_1.
(*** MS END {"type": "configuration", "config_type":"tactics"} *)

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition e_uniq_l_term := (
  (forall a b x : G, x <+> a = x <+> b -> a = b) ->
  (forall a b x : G, a <+> x = b <+> x -> a = b) ->
  (forall a : G, e <+> a = a) ->
  (forall a : G, i a <+> a = e) ->
  (forall a : G, a <+> a = a -> a = e) ->
  (forall a : G, a <+> e = a) ->
  (forall a : G, a <+> i a = e) ->
  (forall a b c : G, a <+> b <+> c = a <+> (b <+> c)) ->
  forall a p : G, p <+> a = a -> p = e
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(* The left identity is unique. *)
(*** MS BEGIN {"type": "proof_definition"} *)
Lemma e_uniq_l : 
  forall a p, 
    p <+> a = a -> 
    p = e.
  (*** MS END {"type": "proof_definition"} *)
Proof. 
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  intros.
  eapply cancel_r.
  erewrite <- id_l in H.
  eauto.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  prep_proof_2;
  hammer.
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
  prep_proof_2;
  reflect e_uniq_l_term;
  check_goal.
  (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
Qed.

(*** MS BEGIN {"type": "configuration", "config_type":"tactics"} *)
Ltac prep_proof_3 := extend_ctx e_uniq_l prep_proof_2.
(*** MS END {"type": "configuration", "config_type":"tactics"} *)

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition inv_uniq_l_term := (
  (forall a p : G, p <+> a = a -> p = e) ->
  (forall a b x : G, x <+> a = x <+> b -> a = b) ->
  (forall a b x : G, a <+> x = b <+> x -> a = b) ->
  (forall a : G, e <+> a = a) ->
  (forall a : G, i a <+> a = e) ->
  (forall a : G, a <+> a = a -> a = e) ->
  (forall a : G, a <+> e = a) ->
  (forall a : G, a <+> i a = e) ->
  (forall a b c : G, a <+> b <+> c = a <+> (b <+> c)) ->
  forall a b : G, a <+> b = e -> a = i b
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(* The left inverse is unique. *)
(*** MS BEGIN {"type": "proof_definition"} *)
Lemma inv_uniq_l : 
  forall a b, 
    a <+> b = e -> 
    a = i b.
  (*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  intros.
  eapply cancel_r.
  erewrite <- inv_l in H.
  eauto.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  prep_proof_3; 
  hammer.
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
  prep_proof_3;
  reflect inv_uniq_l_term;
  check_goal.
  (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
Qed.

(*** MS BEGIN {"type": "configuration", "config_type":"tactics"} *)
Ltac prep_proof_4 := extend_ctx inv_uniq_l prep_proof_3.
(*** MS END {"type": "configuration", "config_type":"tactics"} *)

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition e_uniq_r_term := (
  (forall a b : G, a <+> b = e -> a = i b) ->
  (forall a p : G, p <+> a = a -> p = e) ->
  (forall a b x : G, x <+> a = x <+> b -> a = b) ->
  (forall a b x : G, a <+> x = b <+> x -> a = b) ->
  (forall a : G, e <+> a = a) ->
  (forall a : G, i a <+> a = e) ->
  (forall a : G, a <+> a = a -> a = e) ->
  (forall a : G, a <+> e = a) ->
  (forall a : G, a <+> i a = e) ->
  (forall a b c : G, a <+> b <+> c = a <+> (b <+> c)) ->
  forall a p : G, a <+> p = a -> p = e
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(* The right identity is unique. *)
(*** MS BEGIN {"type": "proof_definition"} *)
Lemma e_uniq_r : 
  forall a p, 
    a <+> p = a -> 
    p = e.
  (*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  intros.
  eapply cancel_l.
  erewrite <- id_r in H.
  eauto.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  prep_proof_4; 
  hammer.
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
  prep_proof_4;
  reflect e_uniq_r_term;
  check_goal.
  (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
Qed.


(*** MS BEGIN {"type": "configuration", "config_type":"tactics"} *)
Ltac prep_proof_5 := extend_ctx e_uniq_r prep_proof_4.
(*** MS END {"type": "configuration", "config_type":"tactics"} *)

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition inv_uniq_r_term := (
  (forall a p : G, a <+> p = a -> p = e) ->
(forall a b : G, a <+> b = e -> a = i b) ->
(forall a p : G, p <+> a = a -> p = e) ->
(forall a b x : G, x <+> a = x <+> b -> a = b) ->
(forall a b x : G, a <+> x = b <+> x -> a = b) ->
(forall a : G, e <+> a = a) ->
(forall a : G, i a <+> a = e) ->
(forall a : G, a <+> a = a -> a = e) ->
(forall a : G, a <+> e = a) ->
(forall a : G, a <+> i a = e) ->
(forall a b c : G, a <+> b <+> c = a <+> (b <+> c)) ->
forall a b : G, a <+> b = e -> b = i a
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(* The right inverse is unique. *)
(*** MS BEGIN {"type": "proof_definition"} *)
Lemma inv_uniq_r : 
  forall a b, 
    a <+> b = e -> 
    b = i a.
  (*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  intros.
  eapply cancel_l.
  erewrite <- inv_r in H.
  eauto.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  prep_proof_5; 
  hammer.
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
  prep_proof_5.
  reflect inv_uniq_r_term;
  check_goal.
  (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
Qed.


(*** MS BEGIN {"type": "configuration", "config_type":"tactics"} *)
Ltac prep_proof_6 := extend_ctx inv_uniq_r prep_proof_5.
(*** MS END {"type": "configuration", "config_type":"tactics"} *)

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition inv_distr_term := (
  (forall a b : G, a <+> b = e -> b = i a) ->
(forall a p : G, a <+> p = a -> p = e) ->
(forall a b : G, a <+> b = e -> a = i b) ->
(forall a p : G, p <+> a = a -> p = e) ->
(forall a b x : G, x <+> a = x <+> b -> a = b) ->
(forall a b x : G, a <+> x = b <+> x -> a = b) ->
(forall a : G, e <+> a = a) ->
(forall a : G, i a <+> a = e) ->
(forall a : G, a <+> a = a -> a = e) ->
(forall a : G, a <+> e = a) ->
(forall a : G, a <+> i a = e) ->
(forall a b c : G, a <+> b <+> c = a <+> (b <+> c)) ->
forall a b : G, i (a <+> b) = i b <+> i a
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(* The right inverse is unique. *)

(* The inverse operator distributes over the group operator. *)
(*** MS BEGIN {"type": "proof_definition"} *)
Lemma inv_distr : 
  forall a b, 
    i (a <+> b) = i b <+> i a.
    (*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  intros.
  eapply eq_sym.
  eapply inv_uniq_r.
  erewrite <- assoc.
  assert (a <+> b <+> i b <+> i a = a <+> (b <+> i b) <+> i a) by (now erewrite <- assoc).
  erewrite H.
  erewrite inv_r.
  erewrite id_r.
  eapply inv_r.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  prep_proof_6; 
  hammer.
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
  prep_proof_6.
  reflect inv_distr_term;
  check_goal.
  (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
Qed.



(*** MS BEGIN {"type": "configuration", "config_type":"tactics"} *)
Ltac prep_proof_7 := extend_ctx inv_distr prep_proof_6.
(*** MS END {"type": "configuration", "config_type":"tactics"} *)

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition double_inv_term := (
  (forall a b : G, i (a <+> b) = i b <+> i a) ->
(forall a b : G, a <+> b = e -> b = i a) ->
(forall a p : G, a <+> p = a -> p = e) ->
(forall a b : G, a <+> b = e -> a = i b) ->
(forall a p : G, p <+> a = a -> p = e) ->
(forall a b x : G, x <+> a = x <+> b -> a = b) ->
(forall a b x : G, a <+> x = b <+> x -> a = b) ->
(forall a : G, e <+> a = a) ->
(forall a : G, i a <+> a = e) ->
(forall a : G, a <+> a = a -> a = e) ->
(forall a : G, a <+> e = a) ->
(forall a : G, a <+> i a = e) ->
(forall a b c : G, a <+> b <+> c = a <+> (b <+> c)) ->
forall a : G, i (i a) = a
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)


(* The inverse of an inverse produces the original element. *)
(*** MS BEGIN {"type": "proof_definition"} *)
Lemma double_inv : 
  forall a, 
    i (i a) = a.
  (*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  intros.
  eapply eq_sym.
  eapply inv_uniq_r.
  eapply inv_l.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  prep_proof_7; 
  hammer.
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
  prep_proof_7.
  reflect double_inv_term;
  check_goal.
  (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
Qed.


(*** MS BEGIN {"type": "configuration", "config_type":"tactics"} *)
Ltac prep_proof_8 := extend_ctx inv_distr prep_proof_7.
(*** MS END {"type": "configuration", "config_type":"tactics"} *)

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition id_inv_term := (
  (forall a b : G, i (a <+> b) = i b <+> i a) ->
(forall a b : G, i (a <+> b) = i b <+> i a) ->
(forall a b : G, a <+> b = e -> b = i a) ->
(forall a p : G, a <+> p = a -> p = e) ->
(forall a b : G, a <+> b = e -> a = i b) ->
(forall a p : G, p <+> a = a -> p = e) ->
(forall a b x : G, x <+> a = x <+> b -> a = b) ->
(forall a b x : G, a <+> x = b <+> x -> a = b) ->
(forall a : G, e <+> a = a) ->
(forall a : G, i a <+> a = e) ->
(forall a : G, a <+> a = a -> a = e) ->
(forall a : G, a <+> e = a) ->
(forall a : G, a <+> i a = e) ->
(forall a b c : G, a <+> b <+> c = a <+> (b <+> c)) -> i e = e
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)



(* The identity is its own inverse. *)
(*** MS BEGIN {"type": "proof_definition"} *)
Lemma id_inv : 
  i e = e.
  (*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  intros.
  eapply eq_sym.
  eapply inv_uniq_r.
  eapply id_r.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  prep_proof_8; 
  hammer.
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
  prep_proof_8.
  reflect id_inv_term;
  check_goal.
  (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
Qed.
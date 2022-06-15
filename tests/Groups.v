
Require Import MirrorSolve.SMT.
Require Import MirrorSolve.BV.


(* pulled from: https://people.cs.umass.edu/~arjun/courses/cs691pl-spring2014/assignments/groups.html *)

(* The set of the group. *)
Parameter G : Set.

(* The binary operator. *)
Parameter f : G -> G -> G.

(* The group identity. *)
Parameter e : G.

(* The inverse operator. *)
Parameter i : G -> G.

(* For readability, we use infix <+> to stand for the binary operator. *)
Infix "<+>" := f (at level 50, left associativity).

(* The operator [f] is associative. *)
Axiom assoc : forall a b c, a <+> b <+> c = a <+> (b <+> c).

(* [e] is the right-identity for all elements [a] *)
Axiom id_r : forall a, a <+> e = a.

(* [i a] is the right-inverse of [a]. *)
Axiom inv_r : forall a, a <+> i a = e.


(* Some group theory results translated into Coq *)

Lemma unique_id : forall a, a <+> a = a -> a = e.
  intros.
  assert (a <+> i a = a <+> i a) by trivial.
  erewrite <- H in H0 at 1.
  erewrite assoc in H0.
  erewrite inv_r in H0.
  erewrite id_r in H0.
  auto.
Qed.


(* [i a] is the left-inverse of [a]. *)
Lemma inv_l : forall a, i a <+> a = e.
Proof.
  intros.
  eapply unique_id.
  erewrite <- assoc.
  erewrite assoc with (a := i a).
  erewrite inv_r.
  erewrite id_r.
  trivial.
Qed.
(* [e] is the left-identity. *)
Lemma id_l : forall a, e <+> a = a.
Proof.
  intros.
  erewrite <- inv_r with (a := a).
  erewrite assoc.
  erewrite inv_l.
  erewrite id_r.
  trivial.
Qed.

(* [x] can be cancelled on the right. *)
Lemma cancel_r : forall a b x, a <+> x = b <+> x -> a = b.
Proof.
  intros.
  assert (a <+> x <+> i x = a <+> x <+> i x) by trivial.
  erewrite H in H0 at 1.
  repeat erewrite assoc in H0.
  repeat erewrite inv_r in H0.
  repeat erewrite id_r in H0.
  auto.
Qed.
  

(* [x] can be cancelled on the left. *)
Lemma cancel_l: forall a b x, x <+> a = x <+> b -> a = b.
Proof.
  intros.
  assert (i x <+> x <+> a = i x <+> x <+> a) by trivial.
  erewrite assoc in H0.
  erewrite H in H0 at 1.
  repeat erewrite <- assoc in H0.
  erewrite inv_l in H0.
  repeat erewrite id_l in H0.
  auto.
Qed.

(* The left identity is unique. *)
Lemma e_uniq_l : forall a p, p <+> a = a -> p = e.
Proof.
  intros.
  eapply cancel_r.
  erewrite <- id_l in H.
  eauto.
Qed.
(* The left inverse is unique. *)
Lemma inv_uniq_l : forall a b, a <+> b = e -> a = i b.
Proof.
  intros.
  eapply cancel_r.
  erewrite <- inv_l in H.
  eauto.
Qed.

(* The left identity is unique. *)
Lemma e_uniq_r : forall a p, a <+> p = a -> p = e.
Proof.
  intros.
  eapply cancel_l.
  erewrite <- id_r in H.
  eauto.
Qed.

(* The right inverse is unique. *)
Lemma inv_uniq_r : forall a b, a <+> b = e -> b = i a.
Proof.
  intros.
  eapply cancel_l.
  erewrite <- inv_r in H.
  eauto.
Qed.

(* The inverse operator distributes over the group operator. *)
Lemma inv_distr : forall a b, i (a <+> b) = i b <+> i a.
Proof.
  intros.
  eapply eq_sym.
  eapply inv_uniq_r.
  erewrite <- assoc.
  assert (a <+> b <+> i b <+> i a = a <+> (b <+> i b) <+> i a) by (now erewrite <- assoc).
  erewrite H.
  erewrite inv_r.
  erewrite id_r.
  eapply inv_r.
Qed.
(* The inverse of an inverse produces the original element. *)
Lemma double_inv : forall a, i (i a) = a.
Proof.
  intros.
  eapply eq_sym.
  eapply inv_uniq_r.
  eapply inv_l.
Qed.
(* The identity is its own inverse. *)
Lemma id_inv : i e = e.
Proof.
  intros.
  eapply eq_sym.
  eapply inv_uniq_r.
  eapply id_r.
Qed.


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

Definition group_model := Groups.fm_model G.

(* First, set up uninterpreted function symbols for the binary operator, the inverse, and the identity *)
Definition symbs : list (string * list (sig_sorts MirrorSolve.Groups.sig) * sig_sorts MirrorSolve.Groups.sig) := ([
  ("op", [G'; G'], G'); (* G -> G -> G *)
  ("inv", [G'], G'); (* G -> G *)
  ("e", [], G')   (* nullary function symbol (i.e. constant) *)
]%string).

(* Make all the conversion proofs transparent to make sure later conversions aren't sticky  *)

(* quicker boolean function for function symbol membership *)
Lemma in_conv : forall {sym a r}, 
  In (sym, a, r) symbs -> 
  in_symbs sig sorts_eq_dec symbs sym a r = true.
Proof.
  eapply UF.in_symbs_corr.
Defined.

Import HListNotations.

(* Interpretation function for UF symbols. 
   In order for the reflection machinery to work out, we need to provide an actual interpretation for the UF symbols (even though they will be discharged as UF symbols in SMT).  *)
Definition interp_syms (sym: string) (a: list (sig_sorts sig)) (r: sig_sorts sig) (H: In (sym, a, r) symbs) (args: HList.t (FirstOrder.mod_sorts sig group_model) a) : FirstOrder.mod_sorts sig group_model r.
  pose proof in_conv H.
  unfold in_symbs in H0.
  simpl in H0.
  repeat match goal with 
  | H: (if (?L =? ?R)%string then _ else _) = _ |- _ => 
    destruct (comp_str_eqb_spec L R)
  | H: (if ?A then _ else _) = _ |- _ => 
    destruct A eqn:?
  end; try congruence;
  subst.
  - inversion args; subst; clear args;
    inversion H4; subst; clear H4.
    exact (f H3 H5).
  - inversion args; subst; clear args.
    exact (i H3).
  - exact e.
Defined.

Definition group_uf_model := UF.fm_model Groups.sig group_model symbs interp_syms.

Require Import MirrorSolve.HLists.
Require Import Coq.Lists.List.

Import HListNotations.
Import ListNotations.

Require Import Coq.Strings.String.

(* Witnesses for each of the group UF memberships *)
Lemma in_op : 
  In ("op"%string, [G'; G'], G') symbs.
Proof.
  simpl.
  left; trivial.
Defined.

Lemma in_inv : 
  In ("inv"%string, [G'], G') symbs.
Proof.
  simpl.
  right.
  left; trivial.
Defined.

Lemma in_e : 
  In ("e"%string, [], G') symbs.
Proof.
  simpl.
  right.
  right.
  left; trivial.
Defined.

Notation sig' := (UF.sig sig symbs).

Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.
Require Import MirrorSolve.Reflection.Tactics.

MetaCoq Quote Definition t_f := f.
MetaCoq Quote Definition t_i := i.
MetaCoq Quote Definition t_e := e.

(* Some match tactics for the meta-interpreter. 
   The meta-interpreter converts these definitions into a reflection procedure between pure Coq goals and FOL terms in the UF + Groups combined theory. 
*)
Program Definition match_tacs : list ((term -> bool) * tac_syn sig' group_uf_model) := [
  ( eq_term t_f, tacFun _ _ {| deep_f := UFun sig symbs in_op |} ); 
  ( eq_term t_i, tacFun _ _ {| deep_f := UFun sig symbs in_inv |} );
  ( eq_term t_e, tacFun _ _ {| deep_f := UFun sig symbs in_e |} )
  ].

MetaCoq Quote Definition g_ind := (G).

(* This is an analogous match but for reflecting Coq types into FOL sorts. *)
Definition match_inds : list (term * Groups.sorts) := [
    (g_ind, G')
  ].

Program Definition mt_wf: match_tacs_wf sig' group_uf_model sorts_eq_dec match_tacs := {| 
  match_tacs_sound_some := _;
  match_tacs_sound_none := _;
|}.
Admit Obligations.
(* Next Obligation.
  repeat match goal with 
  | H: _ \/ _ |- _ => 
    destruct H
  | H: False |- _ => 
    inversion H
  end.
  inversion H.
  simpl in *;
  subst;
  repeat match goal with 
  | |- (if ?X then _ else _) = _ => 
    destruct X eqn:?; simpl in *; try congruence
  | |- match ?X with | Some _ => _ | None => _ end = _ => 
    destruct X eqn:?; simpl in *; try congruence
  end.
Admit Obligations. *)


(* Next we configure the backend solver. We need to tell the OCaml backend about: 
   A custom sort symbol for the Groups.G' sort;
   and custom UF symbols for e, op, and inv. 

   The syntax for a UF declaration is 
    RegisterSMTUF <symbol name as a string> <return sort> <list of argument sorts>
*)
Local Declare ML Module "mirrorsolve".
RegisterCustomSort Groups.G' "G".
RegisterSMTUF "e" G'.
RegisterSMTUF "op" G' G' G'.
RegisterSMTUF "inv" G' G'.

Transparent denote_tm.

Require Import MirrorSolve.Axioms. (* trust the SMT solver in a typesafe way *)

Ltac check_goal := 
  match goal with 
  | |- ?G => check_interp_pos G; eapply UnsoundAxioms.interp_true
  end.

MetaCoq Quote Definition unique_id_term := (
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) -> (* associativity axiom *)
  (forall a, a <+> e = a) -> (* right identity axiom *)
  (forall a, a <+> i a = e) -> (* inverse axiom *)
  (forall a, a <+> a = a -> a = e) (* original goal for unique_id (see above) *)
).

Lemma unique_id' : 
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) -> 
  (forall a, a <+> e = a) -> 
  (forall a, a <+> i a = e) -> 
  (forall a, a <+> a = a -> a = e).
Proof.
  reflect_goal (UF.sig sig symbs) group_uf_model sorts_eq_dec match_tacs match_inds mt_wf unique_id_term.
  check_goal.
Qed.

MetaCoq Quote Definition inv_l_term := (
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  (forall a, i a <+> a = e)
).

Lemma inv_l' : 
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  (forall a, i a <+> a = e).
Proof.
  reflect_goal (UF.sig sig symbs) group_uf_model sorts_eq_dec match_tacs match_inds mt_wf inv_l_term.
  check_goal.
Qed.

MetaCoq Quote Definition id_l_term := (
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  (forall a, e <+> a = a)
).

Lemma id_l' : 
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  (forall a, e <+> a = a).
Proof.
  reflect_goal (UF.sig sig symbs) group_uf_model sorts_eq_dec match_tacs match_inds mt_wf id_l_term.
  check_goal.
Qed.

MetaCoq Quote Definition cancel_r_term := (
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  (forall a b x, a <+> x = b <+> x -> a = b)
).


Lemma cancel_r' : 
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  (forall a b x, a <+> x = b <+> x -> a = b).
Proof.
  reflect_goal (UF.sig sig symbs) group_uf_model sorts_eq_dec match_tacs match_inds mt_wf cancel_r_term.
  check_goal.
Qed.
  
MetaCoq Quote Definition cancel_l_term := (
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  (forall a b x, x <+> a = x <+> b -> a = b)
).

Lemma cancel_l' : 
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  (forall a b x, x <+> a = x <+> b -> a = b).
Proof.
  reflect_goal (UF.sig sig symbs) group_uf_model sorts_eq_dec match_tacs match_inds mt_wf cancel_l_term.
  check_goal.
Qed.

MetaCoq Quote Definition eq_uniq_l_term := (
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  (forall a p, p <+> a = a -> p = e)
).

Lemma eq_uniq_l' : 
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  (forall a p, p <+> a = a -> p = e).
Proof.
  reflect_goal (UF.sig sig symbs) group_uf_model sorts_eq_dec match_tacs match_inds mt_wf eq_uniq_l_term.
  check_goal.
Qed.

MetaCoq Quote Definition inv_uniq_l_term := (
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  (forall a b, a <+> b = e -> a = i b)
).

Lemma inv_uniq_l' : 
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  (forall a b, a <+> b = e -> a = i b).
Proof.
  reflect_goal (UF.sig sig symbs) group_uf_model sorts_eq_dec match_tacs match_inds mt_wf inv_uniq_l_term.
  check_goal.
Qed.

MetaCoq Quote Definition inv_uniq_r_term := (
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  (forall a p, a <+> p = a -> p = e)
).

Lemma inv_uniq_r' : 
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  (forall a p, a <+> p = a -> p = e).
Proof.
  reflect_goal (UF.sig sig symbs) group_uf_model sorts_eq_dec match_tacs match_inds mt_wf inv_uniq_r_term.
  check_goal.
Qed.

MetaCoq Quote Definition inv_distr_term := (
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  (forall a b, i (a <+> b) = i b <+> i a)
).

Lemma inv_distr' : 
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  (forall a b, i (a <+> b) = i b <+> i a).
Proof.
  reflect_goal (UF.sig sig symbs) group_uf_model sorts_eq_dec match_tacs match_inds mt_wf inv_distr_term.
  check_goal.
Qed.

MetaCoq Quote Definition double_inv_term := (
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  (forall a, i (i a) = a)
).

Lemma double_inv' : 
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  (forall a, i (i a) = a).
Proof.
  reflect_goal (UF.sig sig symbs) group_uf_model sorts_eq_dec match_tacs match_inds mt_wf double_inv_term.
  check_goal.
Qed.


MetaCoq Quote Definition id_inv_term := (
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  ( i e = e)
).

Lemma id_inv' : 
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) ->
  (forall a, a <+> e = a) ->
  (forall a, a <+> i a = e) ->
  ( i e = e).
Proof.
  reflect_goal (UF.sig sig symbs) group_uf_model sorts_eq_dec match_tacs match_inds mt_wf id_inv_term.
  check_goal.
Qed.
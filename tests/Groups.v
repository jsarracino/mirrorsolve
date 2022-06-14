
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

Lemma mult_both : 
  forall a b c d1 d2, 
    a <+> c = d1
    -> b <+> c = d2
    -> a = b
    -> d1 = d2.
  crush.
Qed.

Hint Extern 100 (_ = _) =>
match goal with
  | [ _ : True |- _ ] => fail 1
  | _ => assert True by constructor; eapply mult_both 
end.

Hint Resolve inv_r.

Lemma inv_r' : 
  forall x y, 
    x = y <+> i y -> 
    x = e.
Proof.
  crush.
Qed.

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




(* encoding in FOL *)

Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.Groups.

Require Import MirrorSolve.HLists.

Require Import MirrorSolve.UF.

Require Import Coq.Strings.String.

Import ListNotations.

Set Universe Polymorphism.

Notation sig := Groups.sig.

Definition group_model := Groups.fm_model G.

(* Parameter f : G -> G -> G.
Parameter i : G -> G. *)

Definition symbs : list (string * list (sig_sorts MirrorSolve.Groups.sig) * sig_sorts MirrorSolve.Groups.sig) := ([
  ("op", [G'; G'], G');
  ("inv", [G'], G');
  ("e", [], G')
]%string).

Lemma in_conv : forall {sym a r}, 
  In (sym, a, r) symbs -> 
  in_symbs sig sorts_eq_dec symbs sym a r = true.
Proof.
  eapply UF.in_symbs_corr.
Defined.

Import HListNotations.

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
Notation OP := (UFun sig symbs in_op).
Notation INV := (UFun sig symbs in_inv).
Notation E := (UFun sig symbs in_e).

Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.
Require Import MirrorSolve.Reflection.Tactics.

MetaCoq Quote Definition t_f := f.
MetaCoq Quote Definition t_i := i.
MetaCoq Quote Definition t_e := e.

Program Definition match_tacs : list ((term -> bool) * tac_syn sig' group_uf_model) := [
  ( eq_term t_f, tacFun _ _ {| deep_f := UFun sig symbs in_op |} ); 
  ( eq_term t_i, tacFun _ _ {| deep_f := UFun sig symbs in_inv |} );
  ( eq_term t_e, tacFun _ _ {| deep_f := UFun sig symbs in_e |} )
  ].

MetaCoq Quote Definition g_ind := (G).

Definition match_inds : list (term * Groups.sorts) := [
    (g_ind, G')
  ].


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
    (* discharge_equiv_denote_orig; autorewrite with mod_fns; eauto |  *)
    |
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

Local Declare ML Module "mirrorsolve".
RegisterCustomSort Groups.G' "G".
RegisterSMTUF "e" G'.
RegisterSMTUF "op" G' G' G'.
RegisterSMTUF "inv" G' G'.

Require Import MirrorSolve.Axioms.

Import UnsoundAxioms.

Transparent denote_tm.

MetaCoq Quote Definition unique_id_term := (
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) -> 
  (forall a, a <+> e = a) -> 
  (forall a, a <+> i a = e) -> 
  (forall a, a <+> a = a -> a = e)
).

Ltac discharge_equiv_denote_orig := 
  split; 
  intros; [
    repeat match goal with 
    | H: exists _, forall (_: ?T), _ |- _ =>
      let H' := fresh "H" in 
      destruct H as [? H'];
      let v := fresh "v" in 
      evar (v: T);
      specialize (H' v);
      subst v
    | H: forall (_: ?T), exists _, _ |- _ =>
      let v := fresh "v" in 
      evar (v: T);
      specialize (H v);
      subst v
    | H: _ /\ _ |- _ => 
      destruct H
    | H: exists _, _ |- _ => 
      destruct H
    | H: Some _ = Some _ |- _ => 
      erewrite Utils.some_prop in H
    | H: _ = ?X |- _ => subst X
    | H: _ = _ |- _ => 
      erewrite <- H in *;
      clear H
    end;
    intuition eauto | 
    repeat match goal with
    | |- exists _: Prop, _ => eexists
    | |- _ /\ _ => split
    | |- Some _ = Some _ => exact eq_refl
    | |- _ => intros
    end;
    intuition eauto
  ].

Lemma unique_id' : 
  (forall a b c, a <+> b <+> c = a <+> (b <+> c)) -> 
  (forall a, a <+> e = a) -> 
  (forall a, a <+> i a = e) -> 
  (forall a, a <+> a = a -> a = e).
  reflect_goal (UF.sig sig symbs) group_uf_model Groups.sorts_eq_dec match_tacs match_inds unique_id_term.
  
  2: {
    match goal with 
    | |- ?G => check_interp_pos G; eapply interp_true
    end.
  }
  split; intros.
  2: {
    repeat match goal with
    | |- exists _: Prop, _ => eexists
    | |- _ /\ _ => split
    | |- Some _ = Some _ => exact eq_refl
    | |- _ => intros
    end;
    intuition eauto.
    vm_compute in *.
    eapply H; eauto.
    
    (* this is kind of cheating, they're in the context but it's a pain to get them out*)
    eapply assoc. 
    eapply id_r.

  }

  repeat match goal with 
    | H: exists _, forall (_: ?T), _ |- _ =>
      let H' := fresh "H" in 
      destruct H as [? H'];
      let v := fresh "v" in 
      evar (v: T);
      specialize (H' v);
      subst v
    | H: forall (_: ?T), exists _, _ |- _ =>
      let v := fresh "v" in 
      evar (v: T);
      specialize (H v);
      subst v
    | H: _ /\ _ |- _ => 
      destruct H
    | H: exists _, _ |- _ => 
      destruct H
    | H: Some _ = Some _ |- _ => 
      erewrite Utils.some_prop in H
    | H: _ = ?X |- _ => subst X
    | H: _ = _ |- _ => 
      erewrite <- H in *;
      clear H
    end.
  
  - 

    match goal with 
    | H: ?A -> ?B |- _ => 
      assert A by admit
    end.
    specialize (H H3); clear H3.

    match goal with 
    | H: ?A -> ?B |- _ => 
      assert A by admit
    end.
    specialize (H H3); clear H3.

    match goal with 
    | H: ?A -> ?B |- _ => 
      assert A by admit
    end.
    specialize (H H3); clear H3.

    specialize (H a).
    assert (a <+> a = a -> a = e) by admit.
    erewrite H3; 
    intuition eauto.
    admit.
  - vm_compute.
    vm_compute in H3.
    unfold eqb_spec.
    unfold interp_syms.
    match goal with 
    | |- _ = ?X => 
      assert (X = e) by admit
    end.
    erewrite H4.

    eapply H; 
    admit. (* these are all in scope if interp_syms actually reduces to the right thing*)


  (* TODO: for some reason interp_syms is getting gunked up, 
      it looks like the library rewrites are opaque and don't compute well
  *)


Qed.


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







Notation v_c := (VHere _ _ _). 
Notation v_b := (VThere _ _ _ _ v_c).
Notation v_a := (VThere _ _ _ _ v_b).  

(* group axioms *)
(* Axiom assoc : forall a b c, a <+> b <+> c = a <+> (b <+> c). *)
Definition assoc_fol {c} : fm sig symbs c :=
  FForall _ (FForall _ (FForall _ 
    (FEq 
      (TFun sig' OP 
        ( 
          (TFun sig' OP ((TVar v_a) ::: (TVar v_b) ::: hnil)) ::: 
          (TVar v_c) ::: hnil
        ))
      (TFun sig' OP 
        ( 
          (TVar v_a) ::: 
          (TFun sig' OP ((TVar v_b) ::: (TVar v_c) ::: hnil)) ::: hnil
        ))
    )
  )).

(* Axiom id_r : forall a, a <+> e = a. *)
Definition id_r_fol {c} : fm sig symbs c :=
  FForall _ 
    (FEq 
      (TFun sig' OP 
        ( 
          (TVar v_c) ::: (TFun sig' (CFun sig _ ELit) hnil) ::: hnil
        ))
      (TVar v_c)
    ).

  
  (* Axiom inv_r : forall a, a <+> i a = e. *)
Definition inv_r_fol {c} : fm sig symbs c :=
  FForall _ 
    (FEq 
      (TFun sig' OP 
        ( 
          (TVar v_c) ::: 
          (TFun sig' INV (TVar v_c ::: hnil)) ::: hnil
        ))
      (TFun sig' (CFun sig _ ELit) hnil)
    ). 

(* interpret a formula in the context of the group axioms *)

Definition group_fm_fol {c} (f: fm sig symbs c) : fm sig symbs c := 
  FImpl assoc_fol (
    FImpl id_r_fol (
      FImpl inv_r_fol f
    )
  ).

Definition interp_group_fm {c v} (f: fm sig symbs c) : Prop := 
  interp_fm (m := group_uf_model) v (group_fm_fol f).

(* Lemma unique_id : forall a, a <+> a = a -> a = e. *)
Definition unique_id_fol_fm : fm sig symbs (SLNil _) :=
  FForall _ (
    FImpl 
      (FEq 
        (TFun sig' OP (TVar v_c ::: TVar v_c ::: hnil)) 
        (TVar v_c))
      (FEq (TVar v_c) (TFun sig' (CFun sig _ ELit) hnil))
  ).

Notation PLUS := (interp_symbs _ _ _ "op" _ _ _).
Notation NEG := (interp_symbs _ _ _ "inv" _ _ _).

Local Declare ML Module "mirrorsolve".

(* RegisterCustomSort BS "BS".

RegisterSMTUF "power" ZS ZS BS. *)

RegisterCustomSort Groups.G' "G".
RegisterSMTUF "e" G'.
RegisterSMTFun ELit "e" 0.

(* Goal interp_fm (m := group_uf_model) (VEmp _ _)
  (FEq 
    (TFun sig' (CFun sig _ ELit) hnil)
    (TFun sig' (CFun sig _ ELit) hnil)
  ).
Proof.
  match goal with 
  | |- ?G => check_interp_pos G
  end.
Admitted. *)

RegisterSMTUF "op" G' G' G'.
Goal interp_fm (m := group_uf_model) (VEmp _ _)
  (FEq 
    (TFun sig' (CFun sig _ ELit) hnil)
    (TFun sig' (CFun sig _ ELit) hnil)
  ).
Proof.
  match goal with 
  | |- ?G => check_interp_pos G
  end.
Admitted.
RegisterSMTUF "inv" G' G'.

Lemma unique_id_fol : interp_group_fm (v := VEmp _ _) unique_id_fol_fm.
Proof.
  unfold interp_group_fm, unique_id_fol_fm, group_fm_fol.
  set (a := assoc_fol).
  set (b := id_r_fol).
  set (c := inv_r_fol).
  set (d := v_c).
  vm_compute in a, b, c, d.
  subst a.
  subst b.
  subst c.
  subst d.
  match goal with 
  | |- ?G => check_interp_pos G
  end.
Admitted.

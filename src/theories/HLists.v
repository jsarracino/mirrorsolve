From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.EquivDec.

Set Universe Polymorphism.

(* CPDT style heterogeneous lists. *)
Module HList.
  Set Implicit Arguments.
  Section HList.
    Variable A: Type.
    Variable B: A -> Type.
    Inductive t : list A -> Type :=
    | HNil: t nil
    | HCons: forall a rest,
        B a ->
        t rest ->
        t (a :: rest).
  End HList.
  Derive NoConfusion Signature for t.

  Fixpoint mapl {A B} (f: forall a: A, B a) (l: list A): HList.t B l :=
    match l with
    | nil => HNil _
    | cons a l => HCons _ (f a) (mapl f l)
    end.

  Fixpoint map {A B C l} (f: forall a: A, B a -> C a) (hl: t B l): t C l :=
    match hl with
    | HNil _ => HNil _
    | HCons a x hl => HCons _ (f a x) (map f hl)
    end.

  Definition all {A B} (P: forall a: A, B a -> Prop) : forall l, @t A B l -> Prop :=
    fix all_rec l hl :=
      match hl with
        | HNil _ => True
        | HCons a x hlt => P a x /\ all_rec _ hlt
      end.


  Equations get
             {A B}
             `{A_eq_dec: EquivDec.EqDec A eq}
             {ks: list A}
             (x: A)
             (pf: List.In x ks)
             (e: t B ks)
    : B x :=
    get x in_pf (@HCons a _ b rest) :=
      match A_eq_dec x a with
      | left pf => eq_rect_r B b pf
      | right pf' =>
        let rest_pf :=
          match in_pf with
          | or_introl eq_pf => False_ind _ (pf' (eq_sym eq_pf))
          | or_intror rest_pf => rest_pf
          end
        in
        get x rest_pf rest
      end.

  Equations bind
             {A B}
             `{A_eq_dec: EquivDec.EqDec A eq}
             {ks: list A}
             (x: A)
             (v: B x)
             (pf: List.In x ks)
             (e: t B ks)
    : t B ks :=
    bind x v in_pf (@HCons a _ b rest) :=
      match A_eq_dec x a with
      | left pf => HCons a (eq_rect _ B v _ pf) rest
      | right pf' =>
        let rest_pf :=
          match in_pf with
          | or_introl eq_pf => False_ind _ (pf' (eq_sym eq_pf))
          | or_intror rest_pf => rest_pf
          end
        in
          HCons a b (bind x v rest_pf rest)
      end.

  Lemma get_extensionality
        {A B}
        `{A_eq_dec: EquivDec.EqDec A eq}
        {ks: list A} :
    forall (e e': t B ks),
      List.NoDup ks ->
      (forall k pf, get k pf e = get k pf e') ->
      e = e'.
  Proof.
    dependent induction ks.
    - intros.
      dependent destruction e.
      dependent destruction e'.
      reflexivity.
    - intros.
      dependent destruction e.
      dependent destruction e'.
      pose proof (H0 a (or_introl eq_refl)) as H'.
      autorewrite with get in H'.
      replace (A_eq_dec a a) with (@eq_dec _ A_eq_dec a a)
        in H' by reflexivity.
      rewrite EqDec.peq_dec_refl in H'.
      unfold eq_rect_r in H'.
      simpl in H'.
      subst b0.
      f_equal.
      assert (List.NoDup ks) by now inversion H.
      eapply IHks; eauto; intros.
      eauto with datatypes.
      specialize (H0 k (or_intror pf)).
      autorewrite with get in H0.
      destruct (A_eq_dec k a).
      + exfalso.
        inversion H.
        congruence.
      + apply H0.
  Qed.

  Lemma get_proof_irrelevance
        {A B}
        `{A_eq_dec: EquivDec.EqDec A eq}
        {ks: list A} :
    forall (e: t B ks) key pf1 pf2,
      get key pf1 e = get key pf2 e.
  Proof.
    intros.
    induction ks.
    - contradiction.
    - dependent destruction e.
      autorewrite with get.
      destruct (A_eq_dec _ _).
      reflexivity.
      simpl.
      destruct pf1, pf2.
      + unfold equiv, complement in c.
        congruence.
      + unfold equiv, complement in c.
        congruence.
      + unfold equiv, complement in c.
        congruence.
      + apply IHks.
  Qed.

End HList.

Module HListNotations.
  Notation "x ::: xs" := (HList.HCons _ x xs) (at level 60, right associativity).
  Notation "'hnil'" := (HList.HNil _).
End HListNotations.
From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Eqdep.

Import ListNotations.

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

    Lemma hcons_inv : 
      forall a rest (x y: B a) hl hl', 
        @HCons a rest x hl = @HCons a rest y hl' <->
        x = y /\ hl = hl'.
    Proof.
      intuition.
      - inversion H as [].
        inversion_sigma.
        subst.
        erewrite (UIP_refl _ _ H1).
        simpl.
        trivial.
      - inversion H as [].
        inversion_sigma.
        subst.
        erewrite (UIP_refl _ _ H2).
        simpl.
        trivial.
      - subst.
        trivial.
    Qed.
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
    get x in_pf (HCons a b rest') :=
      match A_eq_dec x a with
      | left pf => eq_rect_r B b pf
      | right pf' =>
        let rest_pf :=
            match in_pf with
            | or_introl eq_pf => False_ind _ (pf' (eq_sym eq_pf))
            | or_intror rest_pf => rest_pf
            end
        in
        get x rest_pf rest'
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
  bind x v in_pf (HCons a b rest') :=
    match A_eq_dec x a with
    | left pf => HCons a (eq_rect _ B v _ pf) rest'
    | right pf' =>
      let rest_pf :=
          match in_pf with
          | or_introl eq_pf => False_ind _ (pf' (eq_sym eq_pf))
          | or_intror rest_pf => rest_pf
          end
      in
      HCons a b (bind x v rest_pf rest')
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

  Lemma bind_proof_irrelevance:
    forall A (A_eq_dec: EqDec A eq) B (l: list A) (t: HList.t B l) k v pf pf',
      HList.bind k v pf t =
      HList.bind k v pf' t.
  Proof.
    induction l; intros.
    - simpl in pf.
      tauto.
    - simpl in *.
      dependent destruction t0.
      autorewrite with bind.
      destruct (A_eq_dec k a); eauto.
      destruct pf, pf'; try congruence.
      cbn.
      erewrite IHl; eauto.
  Qed.

  Fixpoint app {A: Type} (f: A -> Type)
             {l1 l2: list A}
             (h1: t f l1)
             (h2: t f l2) : t f (l1 ++ l2).
  Proof.
    destruct l1.
    - exact h2.
    - inversion h1.
      constructor.
      + exact X.
      + apply app.
        * apply X0.
        * apply h2.
  Defined.

  Lemma get_app_l:
    forall A (A_eq_dec: EqDec A eq) B (l1 l2: list A) (t1: t B l1) (t2: t B l2) k pf pf',
      In k l1 ->
      get k pf (app t1 t2) = get k pf' t1.
  Proof.
    intros.
    dependent induction t1.
    - simpl in *.
      tauto.
    - simpl in *.
      destruct (A_eq_dec k a) eqn:?.
      + cbn.
        autorewrite with get.
        now rewrite Heqs.
      + autorewrite with get.
        rewrite Heqs.
        cbn.
        autorewrite with get.
        rewrite Heqs.
        simpl.
        destruct pf; try congruence.
        destruct pf'; try congruence.
        auto.
  Qed.

  Lemma get_app_r:
    forall A (A_eq_dec: EqDec A eq) B (l1 l2: list A) (t1: t B l1) (t2: t B l2) k pf pf',
      ~ In k l1 ->
      get k pf (app t1 t2) = get k pf' t2.
  Proof.
    intros.
    dependent induction t1.
    - simpl in *.
      apply get_proof_irrelevance.
    - cbn.
      autorewrite with get.
      destruct (A_eq_dec k a) eqn:?.
      + exfalso.
        apply H.
        destruct e.
        eauto with datatypes.
      + cbn.
        erewrite IHt1; eauto with datatypes.
  Qed.

  Lemma bind_app_l:
    forall A (A_eq_dec: EqDec A eq) B (l1 l2: list A) (t1: t B l1) (t2: t B l2) k v pf pf',
      bind k v pf (app t1 t2) =
      app (bind k v pf' t1) t2.
  Proof.
    induction l1; intros.
    - cbv in pf'.
      tauto.
    - dependent destruction t1.
      destruct (A_eq_dec k a) eqn:Heq.
      + autorewrite with bind.
        rewrite Heq.
        simpl.
        unfold eq_rect_r, eq_rect.
        destruct e.
        simpl.
        autorewrite with bind.
        rewrite Heq.
        reflexivity.
      + simpl.
        autorewrite with bind.
        rewrite Heq.
        cbn.
        autorewrite with bind.
        rewrite Heq.
        cbn.
        erewrite IHl1.
        eauto.
  Qed.

  Lemma bind_app_r:
    forall A (A_eq_dec: EqDec A eq) B (l1 l2: list A) (t1: t B l1) (t2: t B l2) k v pf pf',
      ~ In k l1 ->
      bind k v pf (app t1 t2) =
      app t1 (bind k v pf' t2).
  Proof.
    induction l1; intros.
    - dependent destruction t1.
      cbn in pf, pf'.
      apply bind_proof_irrelevance.
    - dependent destruction t1.
      destruct (A_eq_dec k a) eqn:Heq.
      + exfalso.
        apply H.
        unfold equiv in *.
        subst a.
        eauto with datatypes.
      + cbn.
        assert (Hnotin: ~ List.In k l1) by eauto with datatypes.
        assert (Hinl1l2: List.In k (l1 ++ l2)) by eauto with datatypes.
        assert (Hinl2: List.In k l2) by eauto with datatypes.
        specialize (IHl1 l2 t1 t2 k v Hinl1l2 pf' Hnotin).
        rewrite <- IHl1.
        autorewrite with bind.
        rewrite Heq.
        cbn.
        erewrite bind_proof_irrelevance; eauto.
  Qed.

  Fixpoint map_inj X A (B: A -> Type) (f: X -> A)
    (l: list X) {struct l} :
      t (fun x => B (f x)) l ->
      t B (List.map f l).
  Proof.
    refine (match l as l' return t (fun x => B (f x)) l' ->
                                             t B (List.map f l')
            with
            | [] => fun h => HNil _
            | x :: xs => fun h => _
            end).
    inversion h.
    exact (HCons _ X0 (map_inj _ _ _ _ _ X1)).
  Defined.

  Lemma get_map_inj:
    forall (X A: Type)
      (A_equiv: Equivalence (@eq A))
      (A_eq_dec: @EqDec A _ A_equiv)
      (X_equiv: Equivalence (@eq X))
      (X_eq_dec: @EqDec X _ X_equiv) (B: A -> Type) (f: X -> A) l (xs: t (fun x => B (f x)) l) k pf pf',
      (forall x y, f x = f y -> x = y) ->
      get (f k) pf (map_inj _ f xs) = get k pf' xs.
  Proof.
    intros.
    induction l.
    - cbv in pf'.
      tauto.
    - simpl in pf.
      dependent destruction xs.
      cbn.
      autorewrite with get.
      destruct (A_eq_dec _ _), (X_eq_dec _ _).
      + unfold equiv in *.
        subst a.
        cbn.
        unfold eq_rect_r.
        erewrite <- !eq_rect_eq.
        reflexivity.
      + pose proof (H _ _ e).
        congruence.
      + congruence.
      + simpl in *.
        destruct pf, pf'; try congruence.
        erewrite IHl; eauto.
  Qed.

  Lemma bind_map_inj:
    forall (X A: Type)
      (A_equiv: Equivalence (@eq A))
      (A_eq_dec: @EqDec A _ A_equiv)
      (X_equiv: Equivalence (@eq X))
      (X_eq_dec: @EqDec X _ X_equiv) (B: A -> Type) (f: X -> A) l (xs: t (fun x => B (f x)) l) k v pf pf',
      (forall x y, f x = f y -> x = y) ->
      bind (f k) v pf (map_inj _ f xs) = map_inj _ f (bind k v pf' xs).
  Proof.
    intros.
    induction l.
    - simpl in pf'.
      tauto.
    - dependent destruction xs.
      simpl.
      autorewrite with bind.
      destruct (X_eq_dec k a) eqn:Heq; cbn.
      + autorewrite with bind.
        destruct (A_eq_dec (f k) (f a)); try congruence.
        f_equal.
        destruct e.
        simpl.
        erewrite eq_rect_eq; eauto.
      + autorewrite with bind.
        simpl.
        destruct (A_eq_dec (f k) (f a)).
        * exfalso.
          apply c.
          apply H.
          apply e.
        * f_equal.
          erewrite IHl.
          eauto.
  Qed.

End HList.

Module HListNotations.
  Notation "x ::: xs" := (HList.HCons _ x xs) (at level 60, right associativity).
  Notation "'hnil'" := (HList.HNil _).
End HListNotations.

Section SnocList.
  Variable (T: Type).
  Inductive snoc_list: Type :=
  | SLNil: snoc_list
  | Snoc: snoc_list -> T -> snoc_list.
  Derive NoConfusion for snoc_list.
End SnocList.

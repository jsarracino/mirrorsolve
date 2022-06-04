
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import MirrorSolve.FirstOrder.

Require Import MetaCoq.Template.All.
Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.
Set Universe Polymorphism.

Require Import MirrorSolve.HLists.

Require Import MirrorSolve.Utils.

Section Meta.
  Set Universe Polymorphism.
  Variable (s: signature).
  Variable (m: model s).

  Variable (sorts_eq_dec: EquivDec.EqDec (s.(sig_sorts)) eq).

  Definition term_ind' : forall P : term -> Prop,
    (forall n : nat, P (tRel n)) ->
    (forall id : ident, P (tVar id)) ->
    (forall (ev : nat) (args : list term), P (tEvar ev args)) ->
    (forall s : Universe.t, P (tSort s)) ->
    (forall t : term,
    P t ->
    forall (kind : cast_kind) (v : term), P v -> P (tCast t kind v)) ->
    (forall (na : aname) (ty : term),
    P ty -> forall body : term, P body -> P (tProd na ty body)) ->
    (forall (na : aname) (ty : term),
    P ty -> forall body : term, P body -> P (tLambda na ty body)) ->
    (forall (na : aname) (def : term),
    P def ->
    forall def_ty : term,
    P def_ty ->
    forall body : term, P body -> P (tLetIn na def def_ty body)) ->
    (forall f : term, P f -> 
        forall args : list term, 
        List.Forall P args ->
        P (tApp f args)) ->
    (forall (c : kername) (u : Instance.t), P (tConst c u)) ->
    (forall (ind : inductive) (u : Instance.t), P (tInd ind u)) ->
    (forall (ind : inductive) (idx : nat) (u : Instance.t),
    P (tConstruct ind idx u)) ->
    (forall (ind_nbparams_relevance : (inductive × nat) × relevance)
      (type_info : term),
    P type_info ->
    forall discr : term,
    P discr ->
    forall branches : list (nat × term),
    P (tCase ind_nbparams_relevance type_info discr branches)) ->
    (forall (proj : projection) (t : term), P t -> P (tProj proj t)) ->
    (forall (mfix : mfixpoint term) (idx : nat), P (tFix mfix idx)) ->
    (forall (mfix : mfixpoint term) (idx : nat), P (tCoFix mfix idx)) ->
    (forall i : Int63.int, P (tInt i)) ->
    (forall f16 : PrimFloat.float, P (tFloat f16)) -> forall t : term, P t :=
  fun (P : term -> Prop) (f : forall n : nat, P (tRel n))
    (f0 : forall id : ident, P (tVar id))
    (f1 : forall (ev : nat) (args : list term), P (tEvar ev args))
    (f2 : forall s : Universe.t, P (tSort s))
    (f3 : forall t : term,
        P t ->
          forall (kind : cast_kind) (v : term), P v -> P (tCast t kind v))
    (f4 : forall (na : aname) (ty : term),
          P ty -> forall body : term, P body -> P (tProd na ty body))
    (f5 : forall (na : aname) (ty : term),
          P ty -> forall body : term, P body -> P (tLambda na ty body))
    (f6 : forall (na : aname) (def : term),
          P def ->
          forall def_ty : term,
          P def_ty ->
          forall body : term, P body -> P (tLetIn na def def_ty body))
    (f7 : forall f7 : term, P f7 -> 
      forall args : list term, 
      List.Forall P args ->
      P (tApp f7 args))
    (f8 : forall (c : kername) (u : Instance.t), P (tConst c u))
    (f9 : forall (ind : inductive) (u : Instance.t), P (tInd ind u))
    (f10 : forall (ind : inductive) (idx : nat) (u : Instance.t),
          P (tConstruct ind idx u))
    (f11 : forall (ind_nbparams_relevance : (inductive × nat) × relevance)
            (type_info : term),
          P type_info ->
          forall discr : term,
          P discr ->
          forall branches : list (nat × term),
          P (tCase ind_nbparams_relevance type_info discr branches))
    (f12 : forall (proj : projection) (t : term), P t -> P (tProj proj t))
    (f13 : forall (mfix : mfixpoint term) (idx : nat), P (tFix mfix idx))
    (f14 : forall (mfix : mfixpoint term) (idx : nat), P (tCoFix mfix idx))
    (f15 : forall i : Int63.int, P (tInt i))
    (f16 : forall f16 : PrimFloat.float, P (tFloat f16)) =>
    fix F (t : term) : P t :=
    match t as t0 return (P t0) with
    | tRel n => f n
    | tVar id => f0 id
    | tEvar ev args => f1 ev args
    | tSort s => f2 s
    | tCast t0 kind v => f3 t0 (F t0) kind v (F v)
    | tProd na ty body => f4 na ty (F ty) body (F body)
    | tLambda na ty body => f5 na ty (F ty) body (F body)
    | tLetIn na def def_ty body =>
        f6 na def (F def) def_ty (F def_ty) body (F body)
    | tApp f17 args => f7 f17 (F f17) args (
        (fix args_F (l: list term) : List.Forall P l := 
          match l with 
          | nil => Forall_nil P 
          | t :: ts => Forall_cons _ (F t) (args_F ts)
          end
        ) args
      )
    | tConst c u => f8 c u
    | tInd ind u => f9 ind u
    | tConstruct ind idx u => f10 ind idx u
    | tCase ind_nbparams_relevance type_info discr branches =>
        f11 ind_nbparams_relevance type_info (F type_info) discr 
          (F discr) branches
    | tProj proj t0 => f12 proj t0 (F t0)
    | tFix mfix idx => f13 mfix idx
    | tCoFix mfix idx => f14 mfix idx
    | tInt i => f15 i
    | tFloat f17 => f16 f17
    end.

  Theorem denote_extract:
    forall t denote_tf extract_tf i2srt (p p': Prop) i j c (v: valu s _ c) fm,
      extract_t2fm s extract_tf i2srt sorts_eq_dec c j t = Some fm -> 
      (denote_t2fm s m sorts_eq_dec denote_tf i2srt v i t <-> interp_fm (m := m) v fm).
  Proof.

  induction t using term_ind'; intros; try now (
    simpl in H;
    inversion H
  ).
  -
    simpl in *.
    destruct (binder_name na) eqn:?.
    + 
      repeat match goal with 
      | H: (match ?X with | _ => _ end) = _ |- _ => 
        destruct X eqn:?; [| inversion H]
      end.


      repeat match goal with 
      | H: Some _ = Some _ |- _ => 
        erewrite some_prop in H; subst
      | H: Some _ = Some _ |- _ => 
        inversion H; subst
      end.
      
      (* clear H1. *)
      clear H.

      autorewrite with interp_fm.
      eapply iff_distribute.
      * eapply IHt1; eauto.
      * eapply IHt2; eauto.
    + 
      repeat match goal with 
      | H: (match ?X with | _ => _ end) = _ |- _ => 
        destruct X eqn:?; try now congruence
      end.

      repeat match goal with 
      | H: Some _ = Some _ |- _ => 
        erewrite some_prop in H; subst
      | H: Some _ = Some _ |- _ => 
        inversion H; subst
      end.

      autorewrite with interp_fm.
      clear H.
      split; intros; eapply IHt2; eauto.

  - 
    autorewrite with denote_t2fm in *.
    autorewrite with extract_t2fm in *.
    repeat destruct (eq_term _ _);
    repeat match goal with 
    | H: Some _ = Some _ |- _ => 
      erewrite some_prop in H; subst
    | H: Some _ = Some _ |- _ => 
      inversion H; subst
    | _ => try now congruence
    | H: (match ?X with | _ => _ end) = _ |- _ => 
      destruct X eqn:?; try now congruence
    end;
    autorewrite with interp_fm;
    (try now intuition eauto);
    repeat match goal with 
    | H: (match ?X with | _ => _ end) = _ |- _ => 
      destruct X eqn:?; try now congruence
    | H: Some _ = Some _ |- _ => 
      erewrite some_prop in H; subst
    | H: Some _ = Some _ |- _ => 
      inversion H; subst
    | _ => try now congruence
    end;
    autorewrite with interp_fm;
    repeat match goal with 
    | H: (match ?X with | _ => _ end) = _ |- _ => 
      destruct X eqn:?; try now congruence
    end;
    (* unfold eq_rect_r in *; simpl in *; *)
    repeat match goal with 
    | H: Forall _ (_ :: _) |- _ => 
      inversion H; subst; clear H
    end.

    (* equality, \/, /\, and ~ *)
    + admit.

      (* TODO: need soundness for denote_tm'
      destruct (denote_tm' _ _ _ _ _ t1) eqn:?.
      destruct (denote_tm' _ _ _ _ _ t2) eqn:?.
      destruct s0.
      destruct s1.
      destruct (sorts_eq_dec x1 x2).

      repeat match goal with 
      | H: Equivalence.equiv _ _ |- _ => 
        cbv in H; subst
      end.
      unfold eq_rect_r; simpl.
      2: {

      } *)
      
    + split; intros.
      * match goal with 
        | H: _ \/ _ |- _ => 
          destruct H
        end; [left | right].
        -- eapply H3; eauto.
        -- eapply H2; eauto.
      * 
        match goal with 
        | H: _ \/ _ |- _ => 
          destruct H
        end; [left; eapply H3 | right; eapply H2]; eauto.
    + intuition.
      eapply H3; eauto.
    + erewrite H3; eauto.
      eapply iff_refl.
  - simpl in *.
    repeat (destruct (eq_term _ _)); 
    (try now congruence);
    repeat match goal with 
    | H: Some _ = Some _ |- _ => 
      erewrite some_prop in H; subst
    | H: Some _ = Some _ |- _ => 
      inversion H; subst
    end;
    autorewrite with interp_fm;
    eapply iff_refl.

  - simpl in *.
    repeat (destruct (eq_term _ _)); 
    (try now congruence);
    repeat match goal with 
    | H: Some _ = Some _ |- _ => 
      erewrite some_prop in H; subst
    | H: Some _ = Some _ |- _ => 
      inversion H; subst
    end;
    autorewrite with interp_fm;
    eapply iff_refl.
  Admitted. 


End Meta.
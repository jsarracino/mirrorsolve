
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import MirrorSolve.FirstOrder.

Require Import MetaCoq.Template.All.
Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.
Set Universe Polymorphism.

Require Import MirrorSolve.HLists.

Require Import MirrorSolve.Utils.
Require Import Coq.Program.Equality.

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
    (forall (ci : case_info) (type_info : predicate term) (discr : term),
        P discr ->
        forall branches : list (branch term),
        P (tCase ci type_info discr branches)) ->
    (forall (proj : projection) (t : term), P t -> P (tProj proj t)) ->
    (forall (mfix : mfixpoint term) (idx : nat), P (tFix mfix idx)) ->
    (forall (mfix : mfixpoint term) (idx : nat), P (tCoFix mfix idx)) -> 
    forall (t: term), P t :=
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
    (f11 : forall (ci : case_info) (type_info : predicate term) (discr : term),
          P discr ->
          forall branches : list (branch term),
          P (tCase ci type_info discr branches))
    (f12 : forall (proj : projection) (t : term), P t -> P (tProj proj t))
    (f13 : forall (mfix : mfixpoint term) (idx : nat), P (tFix mfix idx))
    (f14 : forall (mfix : mfixpoint term) (idx : nat), P (tCoFix mfix idx))
     =>
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
    | tCase ci type_info discr branches =>
      f11 ci type_info discr (F discr) branches
    | tProj proj t0 => f12 proj t0 (F t0)
    | tFix mfix idx => f13 mfix idx
    | tCoFix mfix idx => f14 mfix idx
    end.

  Inductive EquivEnvs {c} : 
    valu s m c ->
    list (option (∑ ty : sig_sorts s, mod_sorts s m ty)) -> 
    list (option (∑ srt : sig_sorts s, tm s c srt)) -> 
    Prop := 
    | equiv_nil   : forall v, EquivEnvs v [] []
    | equiv_cons_none   : 
      forall el er v,
      EquivEnvs v el er -> 
      EquivEnvs v (None :: el) (None :: er)
    | equiv_cons_some  : 
      forall v el er, 
      EquivEnvs v el er -> 
      forall ty tm, 
        EquivEnvs v ((Some (ty; interp_tm v tm)) :: el) (Some (ty; tm) :: er).

  Lemma build_equiv_cons : 
    forall c v el er  ty x y tm mv,
      EquivEnvs (c := c) v el er -> 
      x = Some (ty; mv) -> 
      y = Some (ty; tm) -> 
      mv = interp_tm v tm ->
      EquivEnvs v (x :: el) (y :: er).
  Proof.
    intros.
    subst.
    econstructor; 
    eauto.
  Qed.

  Variable (denote_tf : 
    term ->
    list
      (option
        (∑ ty : sig_sorts s,
            mod_sorts s m ty)) ->
    option
      (∑ ty : sig_sorts s,
        mod_sorts s m ty)).

  Variable (extract_tf : 
    forall c : ctx s,
    term ->
    list (option (∑ srt : sig_sorts s, tm s c srt)) ->
    option (∑ srt : sig_sorts s, tm s c srt)).

  Variable (denote_extract_tf_spec : 
    forall c v t el er ty tm, 
      EquivEnvs v el er -> 
      extract_tf c t er = Some (ty; tm) -> 
      denote_tf t el = Some (ty; interp_tm v tm)
  ). 

  Variable (denote_extract_tf_spec_none : 
    forall c v t el er, 
      EquivEnvs v el er -> 
      extract_tf c t er = None -> 
      denote_tf t el = None
  ).


  Variable (denote_tr : 
    term ->
    list
      (option
        (∑ ty : sig_sorts s,
            mod_sorts s m ty)) ->
    Prop
  ).

  Variable (extract_tr : 
    forall c : ctx s,
      term ->
      list (option (∑ srt : sig_sorts s, tm s c srt)) ->
      option (fm s c)
  ).

  Variable (denote_extract_tr_spec : 
    forall c v t el er fm, 
      EquivEnvs v el er -> 
      extract_tr c t er = Some fm -> 
      (denote_tr t el <-> interp_fm (m := m) v fm)
  ).

  Lemma equiv_envs_map:
    forall c v 
      (dtm: term -> option (∑ ty : sig_sorts s, mod_sorts s m ty))
      (etm: term -> option (∑ srt : sig_sorts s, tm s c srt)),
      (forall t, etm t = None -> dtm t = None) -> 
      (forall t ty tm, etm t = Some (ty; tm) -> dtm t = Some (ty; interp_tm v tm)) -> 
      forall tms,
        EquivEnvs v (map dtm tms) (map etm tms).
  Proof.
    induction tms; try now econstructor.
    simpl.
    destruct (etm _) eqn:?;
    match goal with 
    | H: ∑ _, _ |- _ => 
      destruct H
    | _ => idtac
    end.
    - erewrite H0;
      eauto.
      econstructor.
      eauto.
    - erewrite H;
      eauto;
      econstructor;
      eauto.
  Qed.

  Lemma equiv_envs_map_args:
    forall c v
      (dtm: term -> option (∑ ty : sig_sorts s, mod_sorts s m ty))
      (etm: term -> option (∑ srt : sig_sorts s, tm s c srt))
    args,
      Forall
        (fun t : term =>
          (forall (x : sig_sorts s) (tm : tm s c x),
            etm t = Some (x; tm) ->
            dtm t = Some (x; interp_tm v tm)) /\ 
          (etm t = None -> dtm t = None)) args ->
      EquivEnvs v (map dtm args) (map etm args).
  Proof.
    induction 1; try now econstructor.
    intros.
    simpl.
    destruct H.
    destruct (etm _) eqn:?;
    match goal with 
    | H: ∑ _, _ |- _ => 
      destruct H
    | _ => idtac
    end.
    - erewrite H;
      eauto.
      econstructor.
      eauto.
    - erewrite H1;
      eauto;
      econstructor;
      eauto.
  Qed.

  Lemma interp_snoc_there: 
    forall s m t c v ty mv v',
      interp_tm (VSnoc s m t c v ty) (TVar (VThere s c t mv v')) = interp_tm v (TVar v').
  Proof.
    intros.
    autorewrite with interp_tm.
    autorewrite with find.
    trivial.
  Qed.

  Lemma extract_denote_var : 
    forall c v n ty var,
      extract_var s c n = Some (ty; var) -> 
      denote_var s m v n = Some (ty; interp_tm v (TVar var)).
  Proof.
    induction c;
    dependent destruction v; 
    simpl;
    intros;
    autorewrite with extract_var in *;
    try congruence.
    destruct n.
    - autorewrite with extract_var in *.
      inversion H; subst.
      repeat f_equal.
    - autorewrite with extract_var in H.
      destruct (extract_var _ _ _) eqn:?; try congruence.
      destruct s0.
      inversion H.
      subst x.
      erewrite IHc with (ty := ty);
      eauto.
      f_equal.
  Qed.

  Lemma extract_denote_var_none : 
    forall c (v: valu s m c) n,
      extract_var s c n = None -> 
      denote_var s m v n = None.
  Proof.
    induction c;
    dependent destruction v; 
    simpl;
    intros;
    autorewrite with extract_var in *;
    try congruence.
    destruct n.
    - autorewrite with extract_var in *.
      inversion H.
    - autorewrite with extract_var in H.
      destruct (extract_var _ _ _) eqn:?; [
          destruct s0; congruence
        | 
      ].
      eapply IHc; eauto.
  Qed.


  Lemma denote'_extract'_spec : 
    forall {c v} t, 
      ( forall ty tm,
          extract_t2tm' s extract_tf c t = Some (ty; tm) -> 
          denote_tm' s m denote_tf v t = Some (ty; interp_tm v tm)) /\
      (extract_t2tm' s extract_tf c t = None -> 
        denote_tm' s m denote_tf v t = None).
  Proof.
    induction t using term_ind'; intros;
    try now (
      split; intros;
        [   eapply denote_extract_tf_spec
        | eapply denote_extract_tf_spec_none
      ];
      eauto;
      econstructor
    ).
    - simpl in *.
      destruct (extract_var _ _ _) eqn:?; 
      try (intros; congruence).
      + destruct s0;
        split; try congruence.
        intros.
        inversion H; subst.
        erewrite extract_denote_var;
        eauto.
      + split; intros; try congruence.
        erewrite extract_denote_var_none;
        trivial.
    - simpl in *.
      destruct (extract_tf _ _ _) eqn:?;
      split; try (intros; congruence).
      + destruct s0.
        intros.
        inversion H0; subst.
        eapply denote_extract_tf_spec; 
        eauto.
        eapply equiv_envs_map_args;
        eauto.
      + intros.
        eapply denote_extract_tf_spec_none;
        eauto.
        eapply equiv_envs_map_args; 
        eauto.
    Unshelve.
    all: eauto.
    eapply H.
  Qed.

  Lemma denote'_extract'_spec_some : 
    forall {c v} t x tm, 
      extract_t2tm' s extract_tf c t = Some (x; tm) -> 
      denote_tm' s m denote_tf v t = Some (x; interp_tm v tm).
  Proof.
    intros.
    eapply denote'_extract'_spec.
    eauto.
  Qed.

  Theorem denote_extract_general:
    forall (t : term) i2srt c (v: valu s _ c) fm,
      extract_t2fm s extract_tf extract_tr i2srt sorts_eq_dec c t = Some fm -> 
      (denote_t2fm s m sorts_eq_dec denote_tf denote_tr i2srt v t <-> interp_fm (m := m) v fm).
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
    + 
      pose proof denote'_extract'_spec_some (v := v) t1 _ t3.
      erewrite H; eauto.
      clear H.
      pose proof denote'_extract'_spec_some (v := v) t2 _ t4.
      erewrite H; eauto.
      clear H.

      match goal with
      | H: Equivalence.equiv _ _ |- _ => 
        cbv in H; subst
      end.

      erewrite Heqs1.

      unfold eq_rect_r in *; simpl.
      eapply iff_refl.
      
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
    + erewrite H3; eauto.
      eapply iff_refl.
    + erewrite denote_extract_tr_spec with (v := v);
      eauto; 
      try eapply iff_refl.

      eapply equiv_envs_map_args;
      eauto.
      revert denote_extract_tf_spec.
      revert denote_extract_tf_spec_none.
      clear.
      induction args; econstructor;
      eauto.
      pose proof denote_extract_tf_spec.
      pose proof denote_extract_tf_spec_none.
      intros.
      pose proof (@denote'_extract'_spec c v a).
      intuition.
      
  - simpl in *.
    repeat destruct (eq_inductive _ _);
    (try now congruence);
    repeat match goal with 
    | H: Some _ = Some _ |- _ => 
      erewrite some_prop in H; subst
    | H: Some _ = Some _ |- _ => 
      inversion H; subst; clear H
    end;
    autorewrite with interp_fm;
    eapply iff_refl.
  Qed. 


  Theorem denote_extract : 
    forall t fm i2srt, 
      extract_fm s extract_tf extract_tr i2srt sorts_eq_dec t = Some fm -> 
      (denote_fm s m sorts_eq_dec denote_tf denote_tr i2srt t <-> interp_fm (VEmp _ m) fm).
  Proof.
    intros.
    eapply denote_extract_general.
    eapply H.
  Qed.

End Meta.

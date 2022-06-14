
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

  (* Lemma mk_denote_var : 
    forall (c : ctx s) (v : valu s m c) (x : sig_sorts s) (tm : tm s c x) (n : nat),
  match mk_var s c n with
  | Some s0 => let (srt, v0) := s0 in Some (srt; TVar v0)
  | None => None
  end = Some (x; tm) -> denote_var s m v n = Some (x; interp_tm v tm).
  Proof.
    intros.
    induction c; 
    dependent destruction v; 
    simpl in *; autorewrite with mk_var in *; try congruence.
    destruct (mk_var _ _ _) eqn:?; try congruence.
    destruct s0.
    inversion H; subst.

    assert ()
    destruct n.
    - simpl. autorewrite with mk_var in *.
    specialize (IHc v )
    erewrite Heqo in IHc.

    - inversion H.
      f_equal.
    -
      destruct n.
      + eapply IHn.

  Admitted. *)

  Inductive EquivEnvs {c} : 
    list (option (∑ ty : sig_sorts s, mod_sorts s m ty)) -> 
    list (option (∑ srt : sig_sorts s, tm s c srt)) -> 
    Type := 
    | equiv_nil   : EquivEnvs [] []
    | equiv_cons  : 
      forall el er, 
      EquivEnvs el er -> 
      forall ty v mv tm, 
        mv = interp_tm v tm ->
        EquivEnvs ((Some (ty; mv)) :: el) (Some (ty; tm) :: er).

  Lemma build_equiv_cons : 
    forall c v el er  ty x y tm mv,
      EquivEnvs (c := c) el er -> 
      x = Some (ty; mv) -> 
      y = Some (ty; tm) -> 
      mv = interp_tm v tm ->
      EquivEnvs (x :: el) (y :: er).
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
      EquivEnvs el er -> 
      extract_tf c t er = Some (ty; tm) -> denote_tf t el = Some (ty; interp_tm v tm)
  ).

  Lemma equiv_envs_map:
    forall c v tms,
      EquivEnvs (map (denote_tm' (c := c) s m denote_tf v) tms)
      (map (extract_t2tm' s extract_tf c)
        tms).
  Proof.
    induction tms.
    - simpl.
      econstructor.
    - simpl.
  Admitted.

  Lemma denote_extract_app_spec: 
  forall (c : ctx s) (v : valu s m c) (x : sig_sorts s) 
  (tm : tm s c x) (t : term) (args : list term),
Forall
  (fun t0 : term =>
   forall (x0 : sig_sorts s) (tm0 : FirstOrder.tm s c x0),
   extract_t2tm' s extract_tf c t0 = Some (x0; tm0) ->
   denote_tm' s m denote_tf v t0 = Some (x0; interp_tm v tm0)) args ->
(forall (x0 : sig_sorts s) (tm0 : FirstOrder.tm s c x0),
 extract_t2tm' s extract_tf c t = Some (x0; tm0) ->
 denote_tm' s m denote_tf v t = Some (x0; interp_tm v tm0)) ->
extract_tf c (tApp t args) (map (extract_t2tm' s extract_tf c) args) =
Some (x; tm) ->
denote_tf (tApp t args) (map (denote_tm' s m denote_tf v) args) =
Some (x; interp_tm v tm).
  Proof.
    intros.
    eapply denote_extract_tf_spec; eauto.
  Admitted. 


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
      erewrite interp_snoc_there.
      eapply IHc; eauto.
  Qed.

  Lemma denote'_extract'_spec : 
    forall {c v} t x tm, 
      extract_t2tm' s extract_tf c t = Some (x; tm) -> 
      denote_tm' s m denote_tf v t = Some (x; interp_tm v tm).
  Proof.
    induction t using term_ind'; intros; 
    try (now 
      eapply denote_extract_tf_spec;
      eauto;
      econstructor
    ).
    - simpl in *.
      destruct (extract_var _ _ _) eqn:?; try congruence.
      destruct s0.
      inversion H; subst.
      erewrite extract_denote_var; repeat f_equal; eauto.

    - simpl in *.
      eapply denote_extract_app_spec; 
      eauto.
  Qed.

  Theorem denote_extract_general:
    forall (t : term) i2srt c (v: valu s _ c) fm,
      extract_t2fm s extract_tf i2srt sorts_eq_dec c t = Some fm -> 
      (denote_t2fm s m sorts_eq_dec denote_tf i2srt v t <-> interp_fm (m := m) v fm).
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
      pose proof denote'_extract'_spec (v := v) t1 _ t3.
      erewrite H; eauto.
      clear H.
      pose proof denote'_extract'_spec (v := v) t2 _ t4.
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
  Qed. 


  Theorem denote_extract : 
    forall t fm i2srt, 
      extract_fm s extract_tf i2srt sorts_eq_dec t = Some fm -> 
      (denote_fm s m sorts_eq_dec denote_tf i2srt t <-> interp_fm (VEmp _ m) fm).
  Proof.
    intros.
    eapply denote_extract_general.
    eapply H.
  Qed.

End Meta.

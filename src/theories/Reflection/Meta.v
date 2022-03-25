
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import MirrorSolve.FirstOrder.

Require Import MetaCoq.Template.All.
Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.
Set Universe Polymorphism.

Require Import MirrorSolve.HLists.

Require Import MirrorSolve.Utils.

Require Import Coq.Logic.EqdepFacts.


Module M <: EqdepElimination.
  Monomorphic Axiom eq_rect_eq :
    forall (U:Type) (p:U) (Q:U -> Type) (x:Q p) (h:p = p),
      x = eq_rect p Q x p h.
End M.

Module M' := EqdepTheory(M).

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
    

  Inductive rel_args {c} : list ({ty & option (mod_sorts s m ty)}) -> list (option ({ty & tm s c ty})) -> Type :=
  | RelNil : rel_args nil nil
  | RelConsSome : 
    forall l r ty v v',
      rel_args l r -> 
      rel_args ((existT _ ty (Some v)) :: l) (Some (existT _ ty v') :: r)
  | RelConsNone : 
    forall l r ty, 
      rel_args l r -> 
      rel_args ((existT _ ty None) :: l) (None :: r).

  Definition denote_extract_tf_typs 
    (denote_tf : term -> list ({ty & option (mod_sorts s m ty)}) -> ({ty & option (mod_sorts s m ty)})) 
    (extract_tf: forall c, term -> list (option ({ty & tm s c ty})) -> option ({ty & tm s c ty})) t :=
    forall c env env' ty ty' v v',
       denote_tf t env = existT _ ty (Some v) ->
       extract_tf c t env' = Some (existT _ ty' v') -> 
       ty = ty'.

  (* Fixpoint e2valu {c} (env: list ({ty & option (mod_sorts s m ty)})) : option (valu s m c).
    refine (
      match env with 
      | nil => Some (VEmp _ _)
      | (existT ty (Some v)) :: env' => 
        match e2valu env' with 
        | Some vs => _
        | None => None
        end
      end
    ).
  Admitted. *)

  Definition denote_extract_tf_vs 
    (denote_tf : term -> list ({ty & option (mod_sorts s m ty)}) -> ({ty & option (mod_sorts s m ty)})) 
    (extract_tf: forall c, term -> list (option ({ty & tm s c ty})) -> option ({ty & tm s c ty})) t :=
      forall c env env' ty v v',
        rel_args env env' -> 
        denote_tf t env = existT _ ty (Some v) ->
        extract_tf c t env' = Some (existT _ ty v') -> 
        forall env_v, v = interp_tm env_v v'.

  Require Import Coq.Program.Equality.

  Lemma denote_mk_var_types: 
    forall def_ty c (env: valu s _ c) n ty ty' v v', 
      denote_var s m def_ty env n = existT _ ty (Some v) -> 
      match mk_var s c n with
      | Some s0 => let (srt, v0) := s0 in Some (srt; TVar v0)
      | None => None
      end = Some (existT _ ty' v') -> 
      ty = ty'.
  Proof.
    induction n; induction c; intros; simpl in *.
    - autorewrite with mk_var in H0.
      inversion H0.
    - dependent destruction env.
      simpl in *.
      autorewrite with mk_var in H0.
      inversion H.
      inversion H0.
      trivial.
    - dependent destruction env.
      simpl in H.
      inversion H.
    - 
      dependent destruction env.
      simpl in *.
      admit.
  Admitted.

  Lemma denote_extract'_tm'_types :  
    forall t extract_tf dtf c def_ty (env: valu s _ c) i ty v ty' v',
      denote_extract_tf_typs dtf extract_tf t ->
      denote_tm' s m dtf def_ty env i t = (existT _ ty (Some v)) -> 
      extract_t2tm' s extract_tf c i t = Some (existT _ ty' v') -> 
      ty = ty'. 
  Proof.
    induction t using term_ind'; try now (intros; 
      simpl in *;
      intuition eauto
    ).
    simpl; intros.
    eapply denote_mk_var_types; eauto.
  Qed.

  Lemma denote_extract_rel_args : 
    forall args denote_tf def_ty c (env: valu s _ c) i extract_tf j,
      rel_args (map (denote_tm' s m denote_tf def_ty env i) args) (map (extract_t2tm' s extract_tf c j) args).
  Proof.
    induction args; [intros; econstructor |].
    revert a.
    induction a;
    intros;
    simpl in *.
    
  Admitted.




  Lemma denote_extract'_tm'_corr :  
    forall t denote_tf extract_tf c def_ty (env: valu s _ c) i j ty v v', 
      denote_extract_tf_vs denote_tf extract_tf t ->
      denote_tm' s m denote_tf def_ty env i t = (existT _ ty (Some v)) -> 
      extract_t2tm' s extract_tf c j t = Some (existT _ ty v') -> 
      v = interp_tm env v'.
  Proof.
    induction t using term_ind'; (try now intros;
      simpl in *;
      match goal with 
      | H: denote_extract_tf_vs _ _ _ |- _ => 
        eapply H; eauto; econstructor 
      end
    ); intros.

    - admit.
    - simpl in H1.
      simpl in H2.
      Opaque map.
      eapply H0; eauto.
      eapply denote_extract_rel_args.
  Admitted.

  Lemma denote_extract'_tm'_equiv_forward :  
    forall t s m extract_tf dtf c def_ty (env: valu s _ c) i j ty v, 
      extract_t2tm' s extract_tf c j t = Some (existT _ ty v) -> 
      denote_tm' s m dtf def_ty env i t = (existT _ ty (Some (interp_tm env v))).
  Admitted.

  (* Lemma denote_extract'_tm'_eq :  
    forall t1 t2 s m extract_tf dtf c def_ty (env: valu s _ c) i j ty v ty' v', 
      denote_tm' s m dtf def_ty env i t1 = (existT _ ty (Some v)) ->
      denote_tm' s m dtf def_ty env i t2 = (existT _ ty' (Some v')) -> 
      extract_t2tm' s extract_tf c j t = Some (existT _ ty' v') -> 
      ty = ty'. 
  Admitted. *)

  Require Import Coq.Program.Equality.
  Require Import Coq.Logic.Eqdep_dec.


  Theorem denote_extract':
    forall t denote_tf extract_tf i2srt i j c (v: valu s _ c) fm def_ty p,
      @denote_t2fm s m sorts_eq_dec denote_tf i2srt def_ty c i t = Some p -> 
      extract_t2fm s extract_tf i2srt sorts_eq_dec c j t = Some fm -> 
      (p v <-> interp_fm (m := m) v fm).
  Proof.

  induction t using term_ind'; intros; try now (
    simpl in H;
    inversion H
  ).
  -
    simpl in H.
    simpl in H0.
    destruct (binder_name na) eqn:?.
    + simpl in *.
      repeat match goal with 
      | H: (match ?X with | _ => _ end) = _ |- _ => 
        destruct X eqn:?; [| inversion H]
      end.

      repeat match goal with 
      | H: Some _ = Some _ |- _ => 
        erewrite some_prop in H; subst
      | H: Some _ = Some _ |- _ => 
        progress (inversion H; subst)
      end.
      
      (* clear H1. *)
      clear H0.

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
        progress (inversion H; subst)
      end.

      autorewrite with interp_fm.

      split; intros.

      * specialize (H1 val).
        eapply IHt2 with (p := P); eauto.
      * specialize (H1 x).
        eapply IHt2 with (p := P); eauto.
  - 
    autorewrite with denote_t2fm in *.
    autorewrite with extract_t2fm in *.
    repeat destruct (eq_term _ _);
    repeat match goal with 
    | H: Some _ = Some _ |- _ => 
      erewrite some_prop in H; subst
    | H: Some _ = Some _ |- _ => 
      progress (inversion H; subst)
    | _ => try now congruence
    | H: (match ?X with | _ => _ end) = _ |- _ => 
      destruct X eqn:?; try now congruence
    | H: (match ?X with | _ => _ end) |- _ => 
      destruct X eqn:?; try now congruence
    end;
    autorewrite with interp_fm.
    + unfold pure in H0.
      inversion H0.
      split; trivial.
    
    (* equality, \/, /\, and ~ *)
    +
      destruct args eqn:?; try now congruence.
      destruct l eqn:?; try now congruence.
      destruct l0 eqn:?; try now congruence.
      repeat match goal with 
      | H: Forall _ (_ :: _) |- _ => 
        progress (inversion H; subst; clear H)
      | H: Some _ = Some _ |- _ => 
        progress (inversion H; subst; clear H)
      | H: (match ?X with | _ => _ end) = _ |- _ => 
        destruct X eqn:?; try now congruence
      end.
      unfold eq_rect_r.
      unfold eq_rect.
      destruct (eq_sym _).
      split; intros.
      * repeat match goal with 
        | H: let (_, _) := ?X in _ |- _ => 
          destruct X eqn:?; try now congruence
        | H: (match ?X with | _ => _ end) = _ |- _ => 
          destruct X eqn:?; try now congruence
        | H: match ?X with | _ => _ end |- _ => 
          destruct X eqn:?; try now congruence
        end;
        (try now contradiction);
        autorewrite with interp_fm.
        destruct (eq_sym _); subst.
        (* assert (x1 = x0) by (eapply denote_extract'_tm'_types; eauto). *)
        assert (x1 = x0) by admit.
        subst.
        assert (m1 = interp_tm v t3) by admit.
        eapply denote_extract'_tm'_corr; eauto; [admit|].
        erewrite <- H.
        eauto.
      *  
        autorewrite with interp_fm in H.

        repeat erewrite denote_extract'_tm'_equiv_forward; eauto.

        repeat match goal with 
        | |- match ?X with | _ => _ end => 
          destruct X eqn:?; try now congruence
        end.
        unfold eq_sym.
        assert (e0 = eq_refl) by (eapply M'.UIP_refl).
        erewrite H0.
        trivial.

    
  - simpl in H.
    simpl in H0.
    repeat (destruct (eq_term _ _)); 
    (try now congruence);
    repeat match goal with 
    | H: Some _ = Some _ |- _ => 
      erewrite some_prop in H; subst
    | H: Some _ = Some _ |- _ => 
      progress (inversion H; subst)
    | |- _ => unfold pure in *
    end;
    simpl in *;
    autorewrite with interp_fm;
    eapply iff_refl.

  - simpl in H.
    simpl in H0.
    repeat (destruct (eq_term _ _)); 
    (try now congruence);
    repeat match goal with 
    | H: Some _ = Some _ |- _ => 
      erewrite some_prop in H; subst
    | H: Some _ = Some _ |- _ => 
      progress (inversion H; subst)
    | |- _ => unfold pure in *
    end;
    simpl in *;
    autorewrite with interp_fm;
    eapply iff_refl.
  Admitted.

  


  Lemma denote_extract:
    forall t denote_tf extract_tf i2srt i j c (v: valu s _ c) fm def_ty p p',
      @denote_t2fm s m sorts_eq_dec denote_tf i2srt def_ty c i t = Some p -> 
      extract_t2fm s extract_tf i2srt sorts_eq_dec c j t = Some fm -> 
      (p v <-> p') ->
      (p' <-> interp_fm (m := m) v fm).
  Proof.
    intros.
    erewrite <- H1.
    eapply denote_extract' with (p := p);
    eauto.
  Qed.

End Meta.
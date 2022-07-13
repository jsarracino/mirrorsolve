Require Export MetaCoq.Template.All.
(* Require Import MetaCoq.Checker.All. *)

Require Import MetaCoq.Template.Checker.

Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.

Require Import Coq.Lists.List.

Require Import MirrorSolve.HLists.
Import HListNotations.

Require Import MirrorSolve.Reflection.Meta.

Require Import MirrorSolve.Utils.

Set Universe Polymorphism.

Fixpoint trim_prefix {A} (l: list (option A)) : list (option A) := 
  match l with 
  | None :: l => trim_prefix l
  | _ => l
  end.

Lemma trim_prefix_equiv_envs: 
  forall {s m c v xs ys}, 
    EquivEnvs (c := c) s m v xs ys -> 
    Meta.EquivEnvs s m v (trim_prefix xs) (trim_prefix ys).
Proof.
  induction 1.
  - econstructor.
  - simpl; eauto.
  - simpl; econstructor; eauto.
Qed.

Section Tactics.
  Variable (s: signature).
  Variable (m: model s).

  Notation sorts := (s.(sig_sorts)).
  Notation mod_sorts := (s.(mod_sorts) m).

  Variable (sorts_eq_dec: EquivDec.EqDec (s.(sig_sorts)) eq).


  Fixpoint denote_args (args: list (s.(sig_sorts))) : Type := 
    match args with 
    | nil => unit
    | t :: ts => (denote_args ts * mod_sorts t)%type
    end.

  Fixpoint denote_func (args: list sorts) (ret: sorts): Type := 
    match args with 
    | nil => mod_sorts ret
    | t :: ts => (mod_sorts t -> (denote_func ts ret))%type
    end.

  Fixpoint denote_rel (args: list sorts): Type := 
    match args with 
    | nil => Prop
    | t :: ts => (mod_sorts t -> (denote_rel ts))%type
    end.

  Fixpoint apply_denote_func (arg_tys: list sorts) : forall {ret_ty: sorts} (args: denote_args arg_tys) (f: denote_func arg_tys ret_ty), mod_sorts ret_ty :=
    match arg_tys as atys return 
      (forall ret_ty : sorts,
        denote_args atys ->
        denote_func atys ret_ty -> mod_sorts ret_ty) with 
    | nil => fun _ _ v => v
    | t :: ts => fun _ '(args, arg) f => apply_denote_func ts args (f arg)
    end.
  
  Fixpoint apply_denote_rel (arg_tys: list sorts) : forall (args: denote_args arg_tys) (f: denote_rel arg_tys), Prop :=
    match arg_tys as atys return 
      ( denote_args atys ->
        denote_rel atys -> Prop) with 
    | nil => fun _ v => v
    | t :: ts => fun '(args, arg) f => apply_denote_rel ts args (f arg)
    end.

  Record fun_sym := Mk_fun_sym {
    args_f: list sorts;
    ret: sorts;
    deep_f: s.(sig_funs) args_f ret; 
  }.

  Record rel_sym := Mk_rel_sym {
    args_r: list sorts;
    deep_r: s.(sig_rels) args_r; 
  }.

  Inductive tac_lits := | bool_lit | z_lit | nat_lit | n_lit.


  Definition lit_ty (t: tac_lits) : Type := 
    match t with 
    | bool_lit => bool
    | z_lit => BinNums.Z
    | nat_lit => nat
    | n_lit => BinNums.N
    end.

  Inductive tac_syn :=
    | tacFun : 
      forall (fs: fun_sym), tac_syn
    | tacRel : 
      forall (rs: rel_sym), tac_syn
    | tacLit : 
      forall (lit : tac_lits) (denote_lit: lit_ty lit -> {ty & mod_sorts ty}) (extract_lit: lit_ty lit -> forall c, {ty & tm s c ty}), tac_syn.

  Fixpoint denote_tac_args (tac_args: list sorts) (opt_args: list (option ({ty & mod_sorts ty}))) : option (denote_args tac_args) := 
    match opt_args with 
    | x :: opt_args' => 
      match tac_args as a return option (denote_args a) with 
      | x' :: args' => 
        match x with 
        | Some (existT ty v) =>
          match denote_tac_args args' opt_args' with 
          | Some vs => 
            match sorts_eq_dec x' ty with 
            | left H => Some (vs, eq_rect_r _ v H) 
            | right _ => None
            end
          | None => None
          end
        | None => None
        end
      | nil => None
      end
    | nil => 
      match tac_args as a return option (denote_args a) with 
      | nil => Some tt
      | _ :: _ => None
      end
    end.


  Fixpoint conv_fun {arg_tys ret_ty} {struct arg_tys}: (HList.t mod_sorts arg_tys -> mod_sorts ret_ty) -> denote_func arg_tys ret_ty :=
    match arg_tys with 
    | nil => fun f => f hnil
    | t :: ts => fun f v => 
      conv_fun (fun vs => f (v ::: vs))
    end.

  Eval compute in denote_rel nil.

  Fixpoint conv_rel {arg_tys} {struct arg_tys}: (HList.t mod_sorts arg_tys -> Prop) -> denote_rel arg_tys :=
    match arg_tys with 
    | nil => fun f => f hnil
    | t :: ts => fun f v => 
      conv_rel (fun vs => f (v ::: vs))
    end.

  MetaCoq Quote Definition c_tru := true.
  MetaCoq Quote Definition c_fls := false.

  Definition denote_bool (t: term) : option bool := 
    if eq_term t c_tru then Some true
    else if eq_term t c_fls then Some false
    else None.

  MetaCoq Quote Definition c_nzero := 0%nat.
  MetaCoq Quote Definition c_nsucc := S%nat.

  Definition is_nat_term (t: term) : bool := 
    match t with 
    | tApp f _ => 
      eq_term f c_nsucc
    | _ => eq_term t c_nzero
    end.

  Definition is_bool_term (t: term) : bool := 
    orb (eq_term t c_tru) (eq_term t c_fls).

    

  Fixpoint denote_nat (t: term) : option nat := 
    if eq_term t c_nzero then Some 0
    else 
      match t with 
      | tApp t' [i] => 
        match denote_nat i with 
        | Some i' => 
          if eq_term t' c_nsucc then Some (S i')
          else None
        | _ => None
        end
      | _ => None
      end.

  MetaCoq Quote Definition c_x1 := BinNums.xI.
  MetaCoq Quote Definition c_x0 := BinNums.xO.
  MetaCoq Quote Definition c_xH := BinNums.xH.

  Fixpoint denote_pos (t: term) : option BinNums.positive := 
    if eq_term t c_xH then Some BinNums.xH else
      match t with 
      | tApp t' [i] => 
        match denote_pos i with 
        | Some i' => 
          if eq_term t' c_x1 then Some (BinNums.xI i')
          else if eq_term t' c_x0 then Some (BinNums.xO i')
          else None
        | _ => None
        end
      | _ => None
      end.

  MetaCoq Quote Definition c_zzero := BinNums.Z0.
  MetaCoq Quote Definition c_zpos := BinNums.Zpos.
  MetaCoq Quote Definition c_zneg := BinNums.Zneg.

  Definition denote_Z (t: term) : option BinNums.Z := 
    if eq_term t c_zzero then Some BinNums.Z0 else
      match t with 
      | tApp t' [i] => 
        match denote_pos i with 
        | Some p => 
          if eq_term t' c_zpos then Some (BinNums.Zpos p)
          else if eq_term t' c_zneg then Some (BinNums.Zneg p)
          else None
        | _ => None
        end
      | _ => None
      end.

  Require Import Coq.ZArith.BinIntDef.
  MetaCoq Quote Definition one := (1%Z).

  Definition denote_lit (lit: tac_lits) (t: term) : option (lit_ty lit) :=
    match lit with 
    | bool_lit => denote_bool t
    | z_lit => denote_Z t
    | n_lit => None (* TODO N *)
    | nat_lit => denote_nat t
    end.

  Definition denote_tac_rty : Type := 
    ({ty & mod_sorts ty} + Prop)%type.
  
  Definition denote_tac (tac: tac_syn) (opt_args : list (option ({ty & mod_sorts ty}))) (t: term) : option denote_tac_rty :=
    match tac with 
    | tacFun fs => 
      match denote_tac_args (fs.(args_f)) (trim_prefix opt_args) with 
      | Some wrapped_args => Some (inl (existT _ fs.(ret) (apply_denote_func _ wrapped_args (conv_fun (s.(mod_fns) _ _ _ fs.(deep_f))))))
      | None => None
      end
    | tacRel rs => 
      match denote_tac_args (rs.(args_r)) (trim_prefix opt_args) with 
      | Some wrapped_args => Some (inr (apply_denote_rel _ wrapped_args (conv_rel (s.(mod_rels) _ _ rs.(deep_r)))))
      | None => None
      end
    | tacLit lit dt _ => 
      match denote_lit lit t with 
      | Some dlit => Some (inl (dt dlit))
      | None => None
      end
    end.

  Definition denote_mtac (mtac: (term -> bool) * tac_syn) (t: term) (args: list (option ({ty & mod_sorts ty})%type)) : option denote_tac_rty :=
    let (test, tac) := mtac in 
    if test t then denote_tac tac args t
    else None.
        
  Fixpoint denote_mtacs (mtacs: list ((term -> bool) * tac_syn)) (t: term) (args: list (option ({ty & mod_sorts ty})%type)) : option denote_tac_rty := 
    match mtacs with 
    | nil => None
    | mtac :: mtacs => 
      match denote_mtac mtac t args with 
      | Some r => Some r
      | None => denote_mtacs mtacs t args
      end
    end.

  Equations denote_tm (mtacs: list ((term -> bool) * tac_syn)) (t: term) (args: list (option ({ty & mod_sorts ty}))) : option ({ty & mod_sorts ty}) := 
    denote_tm mtacs (tApp f args) r_args := 
      match denote_mtacs mtacs f r_args with 
      | Some (inl x) => Some x
      | Some _ => None
      | None => 
       (* literal tactics need to be called on the whole term *)
        match denote_mtacs mtacs (tApp f args) r_args with 
        | Some (inl x) => Some x
        | Some _
        | None => None
        end
      end;
    denote_tm mtacs t r_args := 
      match denote_mtacs mtacs t r_args with 
      | Some (inl x) => Some x
      | Some _ 
      | None => None
      end.


  Fixpoint extract_args {c: ctx s} (arg_tys : list sorts) (r_args: list (option ({srt & tm s c srt}))) : option (HList.t (tm s c) arg_tys) :=
    match arg_tys with 
    | nil => 
      match r_args with 
      | nil => Some hnil
      | _ => None
      end
    | a :: args => 
      match r_args with
      | nil => None
      | r :: r_args => 
        match r with 
        | None => None
        | Some r' => 
          let (srt, v) := r' in 
          match sorts_eq_dec a srt with 
          | left H => 
            match extract_args args r_args with 
            | Some hl => Some (eq_rect_r _ v H ::: hl)
            | None => None
            end
          | right _ => None
          end
        end
      end
    end.

  Definition extract_fun {c: ctx s} (fs: fun_sym) (r_args: list (option ({srt & tm s c srt}))) : option ({srt & tm s c srt}) :=
    match extract_args fs.(args_f) (trim_prefix r_args) with 
    | Some fargs => Some (existT _ _ (TFun s fs.(deep_f) fargs))
    | None => None
    end.

  Definition extract_rel {c: ctx s} (rs: rel_sym) (r_args: list (option ({srt & tm s c srt}))) : option (fm s c) :=
    match extract_args rs.(args_r) (trim_prefix r_args) with 
    | Some fargs => Some (FRel _ rs.(deep_r) fargs)
    | None => None
    end.

  Definition extract_rty c : Type := 
    {srt & tm s c srt} + fm s c.

  Definition extract_tac (c: ctx s) (tac: tac_syn) (r_args: list (option ({srt & tm s c srt}))) (t: term) : option (extract_rty c) := 
    match tac with 
    | tacFun fs => 
      match extract_fun fs r_args with 
      | Some x => Some (inl x)
      | None => None
      end
    | tacRel rs => 
      match extract_rel rs r_args with 
      | Some x => Some (inr x)
      | None => None
      end
    | tacLit lit _ ef => 
      match denote_lit lit t with 
      | Some dlit => Some (inl (ef dlit c))
      | None => None
      end
    end.

  Definition extract_mtac (c: ctx s) (mtac: (term -> bool) * tac_syn) (t: term) (r_args: list (option ({srt & tm s c srt}))) : option (extract_rty c) := 
    let (test, tac) := mtac in 
    if test t then extract_tac c tac r_args t
    else None.


  Fixpoint extract_mtacs (c: ctx s) (mtacs: list ((term -> bool) * tac_syn)) (t: term) (r_args: list (option ({srt & tm s c srt}))) : option (extract_rty c) := 
    match mtacs with 
    | nil => None
    | mt :: mtacs => 
      match extract_mtac c mt t r_args with 
      | Some x => Some x
      | None => extract_mtacs c mtacs t r_args
      end
    end.

  Obligation Tactic := intros.
  Equations extract_t2tm {c: ctx s} (mtacs: list ((term -> bool) * tac_syn)) (t: term) (r_args: list (option ({srt & tm s c srt}))) : option ({srt & tm s c srt}) := 
    extract_t2tm mtacs (tApp f args) r_args := 
      match extract_mtacs c mtacs f r_args with 
      | Some (inl v) => Some v
      | Some _ => None
      | None => 
        match extract_mtacs c mtacs (tApp f args) r_args with 
        | Some (inl v) => Some v
        | Some _ 
        | None => None
        end
      end;
    extract_t2tm mtacs t r_args := 
      match extract_mtacs c mtacs t r_args with
      | Some (inl v) => Some v
      | Some _ 
      | None => None
      end.

  Definition extract_t2rel {c: ctx s} (mtacs: list ((term -> bool) * tac_syn)) (t: term) (args : list (option (∑ srt : sorts, tm s c srt))) : option (fm s c) := 
    match extract_mtacs c mtacs t args with 
    | Some (inr f) => Some f
    | Some _ 
    | None => None
    end.

  Definition denote_t2rel (mtacs: list ((term -> bool) * tac_syn)) (t: term) (args: list (option ({ty & mod_sorts ty}))) : Prop := 
    match denote_mtacs mtacs t args with 
    | Some (inr p) => p
    | Some _ => (False -> False)
    | None => False
    end.


  Fixpoint i2srt (minds: list ((term -> bool) * sorts)) (t: term) : option sorts :=
    match minds with 
    | nil => None
    | (f, srt) :: minds => 
      if f t then Some srt else i2srt minds t
    end.

  Variable match_tacs : list ((term -> bool) * tac_syn).
  Variable match_inds : list ((term -> bool) * sorts).

  Lemma extract_denote_args_f_none: 
    forall c (v: valu s m c) el er fs, 
      EquivEnvs s m v el er -> 
      extract_args (args_f fs) er = None -> 
      denote_tac_args (args_f fs) el = None.
  Proof.
    intros.
    destruct fs.
    simpl in  *.
    clear deep_f0.
    revert H0.
    revert H.
    revert el.
    revert er.
    induction args_f0;
    intros;
    simpl in *.
    - destruct H;
      trivial;
      congruence.
    - destruct H;
      simpl in *;
      trivial;
      try congruence.
      destruct (sorts_eq_dec _ _) eqn:?;
      try congruence.
      * destruct (extract_args args_f0 er) eqn:?;
        try congruence.
        erewrite IHargs_f0; eauto.
      * destruct (denote_tac_args args_f0 el); trivial.
  Qed.

  Lemma extract_denote_args_r_none: 
    forall c (v: valu s m c) el er fs, 
      EquivEnvs s m v el er -> 
      extract_args (args_r fs) er = None -> 
      denote_tac_args (args_r fs) el = None.
  Admitted.

  Lemma extract_denote_tac_none: 
    forall c v tac el er t, 
      EquivEnvs s m v el er -> 
      extract_tac c tac er t = None -> 
      denote_tac tac el t = None.
  Proof.
    induction tac; intros; simpl in *;
    unfold extract_fun, extract_rel in *;
    try now (
      destruct (extract_args _ _) eqn:?; 
      try now inversion H0;
      (erewrite extract_denote_args_f_none || erewrite extract_denote_args_r_none); 
      eauto;
      eapply trim_prefix_equiv_envs;
      eauto
    ).
    destruct (denote_lit _ _); eauto.
    inversion H0.
  Qed.

  Lemma extract_denote_mtac_some_inr : 
    forall c v test t el er fm,
      EquivEnvs s m v el er -> 
      extract_mtac c test t er = Some (inr fm) ->
      denote_mtac test t el = Some (inr (interp_fm v fm)).
  Admitted.

  Lemma extract_denote_mtac_none : 
    forall c v test t el er,
      EquivEnvs s m v el er -> 
      extract_mtac c test t er = None ->
      denote_mtac test t el = None.
  Proof.
    intros.
    unfold extract_mtac in H0.
    unfold denote_mtac.
    destruct test.
    destruct (b t); trivial.

    erewrite extract_denote_tac_none; eauto.
  Qed.

  Lemma extract_denote_mtacs_some_inr:
      forall c v el er tests fm t,
        EquivEnvs s m v el er -> 
        extract_mtacs c tests t er = Some (inr fm ) -> 
        denote_mtacs tests t el = Some (inr (interp_fm v fm)).
    Proof.
      induction tests; intros; simpl in *; try now inversion H0.
      destruct (extract_mtac c a t er) eqn:?.
      - destruct e; inversion H0.
        subst.
        erewrite extract_denote_mtac_some_inr; eauto; trivial.
      - erewrite extract_denote_mtac_none; eauto; trivial.
    Qed.

  Lemma extract_denote_mtacs_some_inl:
    forall c v el er tests ty tm t,
      EquivEnvs s m v el er -> 
      extract_mtacs c tests t er = Some (inl (ty; tm)) -> 
      denote_mtacs tests t el = Some (inl (ty; interp_tm v tm)).
  Proof.
  Admitted.
    (* slightly broken... *)
    (* destruct mt_wf.
    destruct t;
    induction tests;
    intros;
    simpl in *;
    try congruence;
    match goal with 
    | H: match ?X with | Some _ => _ | None => _ end = _ |- _ => 
      destruct X eqn:?
    end;
    repeat match goal with 
    | H: extract_mtac _ _ _ _ = Some _ |- _ => 
      erewrite match_tacs_sound_some; eauto
    | H: extract_mtac _ _ _ _ = None |- _ => 
      erewrite match_tacs_sound_none; eauto
    end;
    repeat match goal with
    | X: ∑ _, _ |- _ => 
      destruct X
    | H: Some _ = Some _ |- _ => 
      inversion H; subst; clear H; eauto
    end.
  Qed. *)

  Lemma extract_denote_mtacs_none:
    forall c el er tests t,
      extract_mtacs c tests t er = None -> 
      denote_mtacs tests t el = None.
  Proof.
  Admitted.
    (* destruct mt_wf;
    destruct t; induction tests;
    simpl; intros; trivial;
    match goal with 
    | H : match ?X with | Some _ => _ | None => _ end = _ |- _ => 
      destruct X eqn:?; try congruence
    end;
    erewrite match_tacs_sound_none; eauto.
  Qed. *)


  Lemma extract_denote_mtacs_rel : 
    forall (c : ctx s) (v : valu s m c) (t : term)
      (el : list (option (∑ ty : sorts, mod_sorts ty)))
      (er : list (option (∑ srt : sorts, tm s c srt))) 
      (fm : FirstOrder.fm s c),
    EquivEnvs s m v el er ->
    (fun c0 : ctx s => extract_t2rel match_tacs) c t er = Some fm ->
    denote_t2rel match_tacs t el <-> interp_fm v fm.
  Proof.
    intros.
    simpl in *.
    unfold extract_t2rel in H0.
    unfold denote_t2rel.
    destruct (extract_mtacs c match_tacs t er) eqn:?.
    - destruct e eqn:?; try now inversion H0.
      erewrite extract_denote_mtacs_some_inr; eauto; trivial.
      inversion H0.
      eapply iff_refl.
    - inversion H0.
  Qed.

  Lemma denote_extract_specialized: 
    forall t fm,
      extract_t2fm s (fun c => @extract_t2tm c match_tacs) (fun c => @extract_t2rel c match_tacs) (i2srt match_inds) sorts_eq_dec _ t = Some fm -> 
      (denote_t2fm s m sorts_eq_dec (denote_tm match_tacs) (denote_t2rel match_tacs) (i2srt match_inds) (VEmp _ _) t <-> interp_fm (m := m) (VEmp _ _) fm).
  Proof.
    (* destruct match_tacs_wf as [? [? [? [? ?]]]]. *)
    intros.
    eapply denote_extract_general; eauto.
    - intros.
      simpl in *.
      induction t0 using term_ind';
      autorewrite with denote_tm;
      autorewrite with extract_t2tm in *;
      repeat match goal with 
      | H : match ?X with | Some _ => _ | None => _ end = _ |- _ => 
        destruct X eqn:?; try congruence
      | H : match ?X with | inl _ => _ | inr _ => _ end = _ |- _ => 
        destruct X eqn:?; try congruence
      end;
      try now (
        erewrite extract_denote_mtacs_some_inl; eauto; trivial;
        match goal with 
        | H: Some _ = Some _ |- _ => 
          inversion H; subst
        end;
        eauto
      ).
      erewrite extract_denote_mtacs_none; eauto.
      destruct s0.
      inversion H1.
      erewrite extract_denote_mtacs_some_inl; eauto; trivial.

    - intros.
      induction t0 using term_ind'; 
      autorewrite with denote_tm;
      autorewrite with extract_t2tm in *;
      repeat match goal with 
      | H : match ?X with | Some _ => _ | None => _ end = _ |- _ => 
        destruct X eqn:?; try congruence
      | H : match ?X with | inl _ => _ | inr _ => _ end = _ |- _ => 
        destruct X eqn:?; try congruence
      end;
      match goal with 
      | H: _ = inr _ |- _ => 
        try now (erewrite extract_denote_mtacs_some_inr; eauto)
      | H: _ = None |- _ => 
        try now (erewrite extract_denote_mtacs_none; eauto)
      | _ => idtac
      end.
      + erewrite extract_denote_mtacs_none;
        eauto.
        erewrite extract_denote_mtacs_some_inr;
        eauto.
      + erewrite extract_denote_mtacs_none;
        eauto.
        erewrite extract_denote_mtacs_none;
        eauto.
    - intros.
      eapply extract_denote_mtacs_rel;
      eauto.
  Qed.

  Print Assumptions denote_extract_specialized.

End Tactics.


(* 
Transparent denote_tm.

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

Ltac simpl_extract_tm := exact eq_refl. 

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
      erewrite some_prop in H
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

Ltac reflect_goal sig model srts_eq_dec mtacs minds t' := 
  match goal with 
  | |- ?G => 
    eapply denote_extract_specialized with (s := sig) (m := model) (sorts_eq_dec := srts_eq_dec) (match_tacs := mtacs) (match_inds := minds) (p' := G) (t := t')
  end; [
    simpl_denote_tm |
    simpl_extract_tm |
    discharge_equiv_denote_orig; autorewrite with mod_fns; eauto | 
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
  ]. *)
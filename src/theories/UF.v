
Require Import Coq.Lists.List.

Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.

Require Import Coq.Strings.String.

Set Universe Polymorphism.

Section UF.

  Variable (s: signature).
  Variable (m: model s).

  Set Universe Polymorphism.

  Variable (symbs : list (string * (list s.(sig_sorts)) * s.(sig_sorts))).

  Variable (srt_eq_dec: EquivDec.EqDec s.(sig_sorts) eq).

  Fixpoint in_symbs (symbs : list (string * (list s.(sig_sorts)) * s.(sig_sorts))) (sym: string) (args: list s.(sig_sorts)) (r: s.(sig_sorts)) : bool :=
    match symbs with 
    | nil => false
    | (sym', args', r') :: symbs' => 
      match String.eqb sym sym', list_eq_dec srt_eq_dec args args', srt_eq_dec r r' with 
      | true, left _, left _ => true
      | _, _, _ => in_symbs symbs' sym args r
      end
    end.

  Definition comp_eq_str {x y: string} (opaque_eq: x = y) : x = y :=
    match String.string_dec x y with
    | left transparent_eq => transparent_eq
    | right _ => opaque_eq
    end.

  Require Import Coq.Strings.Ascii.

  Ltac munch_bools bools :=
    match bools with 
    | nil => idtac
    | (?x, ?y) :: ?bools' => 
      refine (
        match x, y with 
        | true, true => _ 
        | false, false => _ 
        | _, _ => ltac:(
          eapply Bool.ReflectF; unfold "<>"; intros H; inversion H)
        end
      ); simpl;
      munch_bools bools'
    end.

  Import ListNotations.
  Definition comp_chr_eqb_spec (x y: ascii) : Bool.reflect (x = y) (x =? y)%char.
    revert y.
    revert x.
    induction x; intros y; 
    destruct y; simpl.
    munch_bools [
      (b, b7); (b0, b8); (b1, b9); (b2, b10);
      (b3, b11); (b4, b12); (b5, b13); (b6, b14)
    ]; econstructor; trivial.
  Defined.

  Definition comp_str_eqb_spec (x y : string) : Bool.reflect (x = y) (x =? y)%string.
    revert y. 
    revert x.
    induction x; intros y;
    destruct y.
    - econstructor; trivial.
    - eapply Bool.ReflectF; intros; congruence.
    - eapply Bool.ReflectF; intros; congruence.
    - simpl.
      destruct (comp_chr_eqb_spec a a0).
      + subst.
        destruct (IHx y); subst.
        * econstructor; trivial.
        * eapply Bool.ReflectF; intros; congruence.
      + eapply Bool.ReflectF; intros; congruence.
  Defined.

  Lemma in_symbs_corr : 
    forall symbs sym a r, 
      in_symbs symbs sym a r = true <-> 
      In (sym, a, r) symbs.
  Proof.
    induction symbs0; intros.
    - simpl;
      split;
      intros H; 
      inversion H.
    - destruct a as [[? ?] ?].
      simpl.
      pose proof comp_str_eqb_spec sym s0.
      inversion H; subst.
      destruct (list_eq_dec _ _ _).
      destruct (srt_eq_dec _ _).
      2-4:
        erewrite IHsymbs0;
        split; intros; intuition eauto.
      + split; intros; intuition eauto.
        left; 
        compute in e0; 
        subst; trivial.
      + inversion H2; subst.
        compute in c.
        contradiction.
      + inversion H2; subst; contradiction.
      + inversion H3; subst; contradiction.
  Defined.

  Variable interp_symbs: 
    forall sym a r, 
    In (sym, a, r) symbs -> 
    HList.t m.(mod_sorts _) a ->
    m.(mod_sorts _) r.

  (* Variable interp_symbs: 
    forall sym a r, 
    in_symbs symbs sym a r = true ->
    HList.t m.(mod_sorts _) a ->
    m.(mod_sorts _) r. *)

  Inductive funs : arity s.(sig_sorts) -> s.(sig_sorts) -> Type := 
  | CFun : forall {a r}, 
    s.(sig_funs) a r -> 
    funs a r
  | UFun : forall {s a r}, 
    In (s, a, r) symbs -> 
    funs a r.

  Definition sig: signature :=
    {| sig_sorts := s.(sig_sorts);
      sig_funs := funs;
      sig_rels := s.(sig_rels) |}.

  Definition fm ctx := FirstOrder.fm sig ctx.
  Definition tm ctx := FirstOrder.tm sig ctx.

  Definition mod_fns params ret (f: sig_funs sig params ret) (args: HList.t m.(mod_sorts _) params) : m.(mod_sorts _) ret :=
    match f in funs a s return HList.t m.(mod_sorts _) a -> m.(mod_sorts _) s with 
    | CFun f =>
      fun args' => m.(mod_fns _) _ _ f args'
    | UFun pf => 
      fun args' => interp_symbs _ _ _ pf args'
    end args.

  Definition mod_sorts (s: sig_sorts sig) : Type := m.(mod_sorts _) s. 

  Definition fm_model : model sig := {|
    FirstOrder.mod_sorts := mod_sorts;
    FirstOrder.mod_fns := mod_fns;
    FirstOrder.mod_rels := m.(mod_rels _);
  |}.

End UF.

Register CFun as ms.uf.cfun.
Register UFun as ms.uf.ufun.
(* 
Section UFFMap.
  Variable (sigA sigB: signature).
  Variable (a_eq_dec: EquivDec.EqDec sigA.(sig_sorts) eq).
  Variable (b_eq_dec: EquivDec.EqDec sigB.(sig_sorts) eq).
  Variable (mA: model sigA).
  Variable (mB: model sigB).

  Variable (a2b : @theory_functor sigA sigB mA mB).

  Variable (fmap_fun_arrs: forall c arr srt, 
    sig_funs sigA arr srt -> 
    HList.t (fun srt' : sig_sorts sigA => FirstOrder.tm sigB (fmap_ctx sigA sigB mA mB a2b c) (a2b.(fmap_sorts) srt')) arr ->
    HList.t (FirstOrder.tm sigB (fmap_ctx sigA sigB mA mB a2b c)) (fmap_arity (a2b.(fmap_sorts)) arr)
  ).

  Variable (fmap_rel_arrs: forall c arr, 
    sig_rels sigA arr -> 
    HList.t (fun srt' : sig_sorts sigA => FirstOrder.tm sigB (fmap_ctx sigA sigB mA mB a2b c) (a2b.(fmap_sorts) srt')) arr ->
    HList.t (FirstOrder.tm sigB (fmap_ctx sigA sigB mA mB a2b c)) (fmap_arity a2b.(fmap_sorts) arr)
  ).

  Variable (fmap_fm_fforall_op : 
    forall c s, 
      FirstOrder.fm sigB (fmap_ctx sigA sigB mA mB a2b (Snoc _ c s)) -> 
      FirstOrder.fm sigB (fmap_ctx sigA sigB mA mB a2b (Snoc _ c s))
  ).

  Variable (a2b_wf : functor_wf sigA sigB mA mB a2b fmap_fun_arrs fmap_rel_arrs fmap_fm_fforall_op).

  Variable (symbsA : list (string * list (sigA.(sig_sorts)) * sigA.(sig_sorts))).

  Fixpoint fmap_symbs (sA: list (string * list (sigA.(sig_sorts)) * sigA.(sig_sorts))) : list (string * list (sigB.(sig_sorts)) * sigB.(sig_sorts)) := 
    match sA with 
    | nil => nil
    | (s, arr, r) :: sAs => 
      (s, fmap_arity a2b.(fmap_sorts) arr, a2b.(fmap_sorts) r) :: fmap_symbs sAs
    end.

  Definition symbsB : list (string * list (sigB.(sig_sorts)) * sigB.(sig_sorts)) := 
    fmap_symbs symbsA.

  Variable (
    interp_symA : (
      forall (sym : string) (a : list sigA.(sig_sorts)) (r : sigA.(sig_sorts)),
        In (sym, a, r) symbsA ->
        HList.t (FirstOrder.mod_sorts sigA mA) a -> 
        FirstOrder.mod_sorts sigA mA r
      )
    ).

  Axiom (
    interp_symB : (
      forall (sym : string) (a : list sigB.(sig_sorts)) (r : sigB.(sig_sorts)),
        In (sym, a, r) symbsB ->
        HList.t (FirstOrder.mod_sorts sigB mB) a -> 
        FirstOrder.mod_sorts sigB mB r
      )
    ).

  Lemma list_eqd_fmap_inlr: 
    forall l r pf pf', 
      list_eq_dec a_eq_dec l r = left pf ->  
      list_eq_dec b_eq_dec (fmap_arity a2b.(fmap_sorts) l) (fmap_arity a2b.(fmap_sorts) r) = right pf' -> 
      False.
  Proof.
    destruct l; destruct r; simpl; intros; congruence.
  Defined.

  Variable (a_b_eqd_inlr : 
    forall l r pf pf', 
      a_eq_dec l r = left pf -> 
      b_eq_dec (a2b.(fmap_sorts) l) (a2b.(fmap_sorts) r) = right pf' -> 
      False
  ).

  Variable (a_b_eqd_inrl : 
    forall l r pf pf', 
      a_eq_dec l r = right pf -> 
      b_eq_dec (a2b.(fmap_sorts) l) (a2b.(fmap_sorts) r) = left pf' -> 
      False
  ).

  Lemma list_eqd_fmap_inrl: 
    forall l r pf pf', 
      list_eq_dec a_eq_dec l r = right pf ->  
      list_eq_dec b_eq_dec (fmap_arity a2b.(fmap_sorts) l) (fmap_arity a2b.(fmap_sorts) r) = left pf' -> 
      False.
  Proof.
    induction l; destruct r; simpl; intros; try congruence.
  Admitted.

  Lemma in_symbs_symbB :
    forall l s args r,
    in_symbs sigA a_eq_dec l s args r = true <-> 
    in_symbs sigB b_eq_dec (fmap_symbs l) s (fmap_arity (fmap_sorts a2b) args) (fmap_sorts a2b r) = true.
  Proof.
    induction l;
    intros;
    try eapply iff_refl. 
    simpl fmap_symbs.
    destruct a.
    destruct p.
    simpl in_symbs.
    destruct (s =? s1)%string eqn:?; [|eapply IHl].
    destruct (list_eq_dec _ _ _) eqn:?.
    - destruct (list_eq_dec b_eq_dec _ _) eqn:?.
      + destruct (a_eq_dec _ _) eqn:?;
        destruct (b_eq_dec _ _) eqn:?;
        try (eapply iff_refl || eapply IHl);
        exfalso.
        * eapply a_b_eqd_inlr; eauto.
        * eapply a_b_eqd_inrl; eauto.
      
      + exfalso; eapply list_eqd_fmap_inlr; eauto.
    - destruct (list_eq_dec b_eq_dec _ _) eqn:?; [| eapply IHl].
      exfalso; eapply list_eqd_fmap_inrl; eauto.
  Defined.

  Definition in_symbB {s args r l} (pf: In (s, args, r) l) : In (s, (fmap_arity (fmap_sorts a2b) args), fmap_sorts a2b r) (fmap_symbs l).
  Proof.
    eapply in_symbs_corr.
    eapply in_symbs_symbB.
    eapply in_symbs_corr.
    eauto.
  Defined.

  Notation sigA' := (sig sigA symbsA).
  Notation sigB' := (sig sigB symbsB).

  Definition fmap_s_funs : 
    forall (arr : arity (sig_sorts sigA)) (srt : sig_sorts sigA),
      funs sigA symbsA arr srt ->
      sig_funs sigB'
    (fmap_arity (fmap_sorts a2b) arr) (fmap_sorts a2b srt). refine (
      fun arr srt fs =>
      match fs
      with 
      | CFun _ _ f => CFun _ _ (a2b.(fmap_funs) _ _ f) 
      | UFun _ _ pf => UFun _ _ (in_symbB pf)
      end).
  Defined.

 Lemma arity_eta {arr}: 
  (@fmap_arity _ sigB' (fun srt0 : sig_sorts sigA' => fmap_sorts a2b srt0) arr) = (fmap_arity (fmap_sorts a2b) arr).
  Proof.
    induction arr; trivial.
    simpl.
    f_equal.
    trivial.
  Defined.

  Notation mA' := (fm_model sigA mA symbsA interp_symA).
  Notation mB' := (fm_model sigB mB symbsB interp_symB).

  Definition a2b_lifted: @theory_functor sigA' sigB' mA' mB'.
  refine ({|
    fmap_sorts := fun (srt : sigA'.(sig_sorts)) => (a2b.(fmap_sorts) srt) : sigB'.(sig_sorts);
    fmap_funs := fun arr srt f => 
      eq_rect_r (fun a : arity (sig_sorts sigB') =>
      sig_funs sigB' a (fmap_sorts a2b srt)) (fmap_s_funs arr srt f) arity_eta;
    fmap_rels := fun arr f => 
      eq_rect_r
      (fun a : arity (sig_sorts sigB') =>
       sig_rels sigB' a) (a2b.(fmap_rels) arr f) arity_eta;
    fmap_mv := fun srt mv => _;
  |}).
  eapply a2b.(fmap_mv).
  exact mv.
  Defined.

  Lemma fmap_ctx_equiv: 
    forall c, (fmap_ctx sigA sigB mA mB a2b c) = (fmap_ctx sigA' sigB' mA' mB' a2b_lifted c).
  Admitted.

  Lemma ctx_ty_equiv: 
    ctx sigA' = ctx sigA.
  Proof. trivial. Defined.




  Definition fmap_fun_arrs' {c arr srt} 
    (fs: sig_funs sigA' arr srt)
    (args: HList.t (fun srt' : sig_sorts sigA' => FirstOrder.tm sigB' (fmap_ctx sigA' sigB' mA' mB' a2b_lifted c) (a2b_lifted.(fmap_sorts) srt')) arr) : 
    HList.t (FirstOrder.tm sigB' (fmap_ctx sigA' sigB' mA' mB' a2b_lifted c)) (fmap_arity (a2b_lifted.(fmap_sorts)) arr).
  erewrite <- fmap_ctx_equiv in *.
  simpl in *.
  eapply fmap_fun_arrs.

 

  Equations fmap_fun_arrs (c: ctx sigA') (arr: arity sigA'.(sig_sorts)) (srt: sigA'.(sig_sorts)) (f: sig_funs sigA' arr srt) (args: HList.t 

  Check fmap_fm _ _ _ _ _ _ _ _.
  Theorem fmap_symbs_corr: 
    forall (c: ctx (sig sigA symbsA)) (v: valu _ _ c) f, 
      interp_fm v f <-> 
      interp_fm (fmap_valu _ _ _ _ as2bs v) (fmap_fm _ _ _ _ as2bs _ _ _ f).
  Proof.

  

End FMap. *)

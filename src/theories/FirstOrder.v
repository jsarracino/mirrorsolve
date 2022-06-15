From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import MirrorSolve.HLists.

Import HListNotations.

Set Universe Polymorphism.

Definition arity sorts := list sorts.

(* a FOL signature is a: 
   1) set of sorts (e.g. Z, B, BV(n)), 
   2) function symbols indexed by argument sorts and return sort (e.g. plus: Z -> Z -> Z)
   3) relation symbols indexed by argument sorts 
*)
Record signature: Type :=
  { sig_sorts: Type;
    sig_funs: arity sig_sorts -> sig_sorts -> Type;
    sig_rels: arity sig_sorts -> Type }.

Section FOL.
  Variable sig: signature.

  (* de Bruijn variable context (i.e. sorts for variables) *)
  Definition ctx := snoc_list sig.(sig_sorts).

  Notation CSnoc := (Snoc sig.(sig_sorts)).
  Notation CEmp := (SLNil sig.(sig_sorts)).

  Import HListNotations.

  (* de Bruijn variables. *)

  Inductive var: ctx -> sig.(sig_sorts) -> Type :=
  | VHere:
    forall ctx s,
      var (CSnoc ctx s) s
  | VThere:
    forall ctx s s',
      var ctx s' ->
      var (CSnoc ctx s) s'.
  Derive Signature NoConfusion for var.

  (* First-order terms (either functions or variables). *)
  Inductive tm: ctx -> sig.(sig_sorts) -> Type :=
  | TVar: 
    forall c s,
      var c s ->
      tm c s
  | TFun:
    forall c args ret,
      sig.(sig_funs) args ret ->
      HList.t (tm c) args ->
      tm c ret.
  Derive Signature for tm.

  Section Tm_Ind.

    Variable (P: forall (c: ctx) (srt: sig_sorts sig), tm c srt -> Prop).

    (* custom induction principle that processes the arguments of functions *)
    Definition tm_ind'
      (PV : forall c s v, P c s (TVar c s v))
      (PF: forall c args ret srt (hl : HList.t (tm c) args),
        HList.all (fun srt => P c srt) hl ->
        P c ret (TFun c args ret srt hl)) :
      forall c srt tm, P c srt tm :=
      fix tirec (c: ctx) (srt: sig_sorts sig) (t: tm c srt) {struct t} :=
      match t with
      | TVar c' s' v => PV c' s' v
      | TFun c' args ret srt' hl => PF _ _ _ _ _
        ((fix hlrec l h {struct h} :=
          match h as h' return
            HList.all (fun srt : sig_sorts sig => P c' srt) h' with
          | hnil => I
          | x ::: hlt => conj (tirec _ _ x) (hlrec _ hlt)
          end
        ) args hl)
      end.
  End Tm_Ind.

  (* First-order formulas. *)
  Inductive fm: ctx -> Type :=
  (* True and False *)
  | FTrue: forall c, fm c
  | FFalse: forall c, fm c
  (* Equality *)
  | FEq: 
    forall c s,
      tm c s ->
      tm c s ->
      fm c
  (* A relation (with arguments) *)
  | FRel:
      forall c args,
        sig.(sig_rels) args ->
        HList.t (tm c) args ->
        fm c
  (* Negation, disjunction, conjunction, and implication *)
  | FNeg: forall c, fm c -> fm c
  | FOr: forall c, fm c -> fm c -> fm c
  | FAnd: forall c, fm c -> fm c -> fm c
  | FImpl: forall c, fm c -> fm c -> fm c
  (* Quantification *)
  | FForall:
    forall c s,
      fm (CSnoc c s) ->
      fm c.
  Derive Signature for fm.

  (* A model defines how to *interpret* the sorts, function symbols, and the relation symbols. *)
  Record model :=
    { mod_sorts: sig.(sig_sorts) -> Type;
      mod_fns: 
        forall args ret,
          sig.(sig_funs) args ret ->
          HList.t mod_sorts args ->
          mod_sorts ret;
      mod_rels: 
        forall args,
          sig.(sig_rels) args ->
          HList.t mod_sorts args ->
          Prop 
    }.

  Section Interp.
    Variable (m: model).

    (* Variable environments, indexed by a typing context *)

    Inductive valu : ctx -> Type :=
    | VEmp: valu CEmp
    | VSnoc: 
      forall s c,
        valu c ->
        m.(mod_sorts) s ->
        valu (CSnoc c s).
    Derive Signature for valu.

    (* Variable evaluation. Because variables are type-indexed by their context, we can implement a total function. *)

    Equations find {c s} (x: var c s) (v: valu c) : m.(mod_sorts) s :=
      { find (VHere _ _) (VSnoc _ _ _ val) := val;
        find (VThere _ _ _ x') (VSnoc _ _ v' _) := find x' v' }.

    (* term evaluation *)

    Equations interp_tm (c: ctx) (s: sig_sorts sig) (v: valu c) (t: tm c s) : m.(mod_sorts) s
      by struct t :=
      { interp_tm _ _ v (TVar c s x) :=
          find x v;
        interp_tm _ _ v (TFun c typs rets fn args) :=
          m.(mod_fns) typs rets fn (interp_tms _ _ v args) }
    where interp_tms (c: ctx) typs (v: valu c) (args: HList.t (tm c) typs) : HList.t m.(mod_sorts) typs
      by struct args :=
      { interp_tms _ _ _ hnil := hnil;
        interp_tms _ _ _ (tm ::: args') :=
          interp_tm _ _ v tm ::: interp_tms _ _ v args' }.

    (* formula evaluation as a Prop *)

    Equations interp_fm (c: ctx) (v: valu c) (f: fm c) : Prop
      by struct f :=
      { interp_fm _ v (FTrue _) := True;
        interp_fm _ v (FFalse _) := False;
        interp_fm _ v (FRel c typs rel args) :=
          m.(mod_rels) typs rel (interp_tms c _ v args);
        interp_fm _ v (FEq c s t1 t2) :=
          interp_tm c s v t1 = interp_tm c s v t2;
        interp_fm _ v (FNeg _ f) :=
          ~ interp_fm _ v f;
        interp_fm _ v (FOr _ f1 f2) :=
          interp_fm _ v f1 \/ interp_fm _ v f2;
        interp_fm _ v (FAnd _ f1 f2) :=
          interp_fm _ v f1 /\ interp_fm _ v f2;
        interp_fm _ v (FImpl _ f1 f2) :=
          interp_fm _ v f1 -> interp_fm _ v f2;
        interp_fm _ v (FForall c s f) :=
          forall val: m.(mod_sorts) s,
            interp_fm (CSnoc c s) (VSnoc _ _ v val) f }.

    (* A few tactics for converting between normal Prop goals and interp_fm goals  *)
    Lemma eq_interp:
      forall c srt v l r, 
        (interp_tm c srt v l = interp_tm c srt v r)
          <-> 
        interp_fm c v (FEq _ _ l r).
    Proof.
      intros.
      autorewrite with interp_fm.
      apply iff_refl.
    Qed.

    Lemma neg_interp:
      forall c v f, 
        (~ interp_fm c v f)
          <-> 
        interp_fm c v (FNeg _ f).
    Proof.
      intros.
      autorewrite with interp_fm.
      apply iff_refl.
    Qed.

    (* Require Import Coq.Logic.JMeq.
    Lemma forall_interp:
      forall c srt v (F : mod_sorts m srt -> fm (CSnoc c srt)) t', 
        (forall t, 
          F (interp_tm (CSnoc c _) srt (VSnoc _ _ t v) (TVar (CSnoc c _) _ (VHere c _ ))) = t' ->
          interp_fm _ v (FForall _ _ t')) <-> forall t, interp_fm _ (VSnoc _ _ t v) (F t).
    Admitted. *)
  End Interp.


  Fixpoint app_ctx (c1 c2: ctx): ctx :=
    match c2 with
    | SLNil _ => c1
    | Snoc _ c2' sort => CSnoc (app_ctx c1 c2') sort
    end.

  Fixpoint ccons s (c: ctx) :=
    match c with
    | SLNil _ => CSnoc CEmp s
    | Snoc _ c s0 => CSnoc (ccons s c) s0
    end.

  Fixpoint app_ctx' (c1 c2: ctx): ctx :=
    match c1 with
    | SLNil _ => c2
    | Snoc _ c1' sort => app_ctx' c1' (ccons sort c2)
    end.

  Equations app_valu
             {m: model}
             {c c': ctx}
             (v: valu m c)
             (v': valu m c')
    : valu m (app_ctx c c') :=
    { app_valu v (VEmp _) := v;
      app_valu v (VSnoc _ _ _ v' x) := VSnoc _ _ _ (app_valu v v') x }.

  Equations vcons {c s m} (x: mod_sorts m s) (v: valu m c) : valu m (ccons s c) :=
    { vcons x (VEmp _) := VSnoc _ _ _ (VEmp _) x;
      vcons x (VSnoc _ _ _ v y) := VSnoc _ _ _ (vcons x v) y }.

  Equations app_valu'
             {m: model}
             {c c': ctx}
             (v: valu m c)
             (v': valu m c')
    : valu m (app_ctx' c c') :=
    { app_valu' (VEmp _) v' := v';
      app_valu' (VSnoc _ _ _ v x) v' := app_valu' v (vcons x v') }.

  Lemma app_ctx_emp_l:
    forall c,
      c = app_ctx CEmp c.
  Proof.
    induction c.
    - reflexivity.
    - simpl.
      congruence.
  Defined.

  Lemma app_ctx_app_ctx':
    forall c1 c2,
      app_ctx c1 c2 = app_ctx' c1 c2.
  Proof.
    induction c1; induction c2; intros; simpl.
    - reflexivity.
    - rewrite <- app_ctx_emp_l.
      reflexivity.
    - rewrite <- IHc1.
      simpl.
      reflexivity.
    - rewrite IHc2.
      simpl.
      rewrite <- IHc1.
      cbn.
      rewrite <- IHc1.
      simpl.
      reflexivity.
  Defined.

  Lemma app_ctx'_app_ctx:
    forall c1 c2,
      app_ctx' c1 c2 = app_ctx c1 c2.
  Proof.
    intros.
    apply eq_sym.
    apply app_ctx_app_ctx'.
  Defined.

  Fixpoint quantify {c0: ctx} (c: ctx): fm (app_ctx c0 c) -> fm c0 :=
    match c as c' return fm (app_ctx c0 c') -> fm c0 with
    | SLNil _ => fun f => f
    | Snoc _ c' sort => fun f => quantify c' (FForall _ _ f)
    end.

  Lemma quantify_correct:
    forall m c c' (v': valu m c') phi,
     interp_fm m c' v' (quantify c phi) <->
     forall valu,
       interp_fm m (app_ctx c' c) (app_valu v' valu) phi.
  Proof.
    induction c.
    - cbn.
      intuition.
      + dependent destruction valu0.
        assumption.
      + specialize (H (VEmp _)).
        autorewrite with app_valu in *.
        assumption.
    - cbn.
      intuition.
      + cbn in *.
        dependent destruction valu0.
        rewrite IHc in H.
        specialize (H valu0).
        autorewrite with app_valu interp_fm in *.
        eauto.
      + rewrite IHc.
        intros v.
        autorewrite with interp_fm.
        intros.
        pose (VSnoc _ _ _ v val) as v''.
        specialize (H v'').
        eauto.
  Qed.

  Equations quantify_all {c: ctx} (f: fm c): fm CEmp := {
    @quantify_all (CSnoc c _) f := quantify_all (FForall _ _ f);
    @quantify_all CEmp f := f
  }.

  Lemma quantify_all_correct:
    forall m c phi,
     interp_fm m CEmp (VEmp _) (quantify_all phi) <->
     forall valu,
       interp_fm m c valu phi.
  Proof.
    dependent induction c; intros.
    - autorewrite with quantify_all.
      firstorder.
      now dependent destruction valu0.
    - autorewrite with quantify_all.
      rewrite IHc.
      split; intros.
      + dependent destruction valu0.
        specialize (H valu0).
        autorewrite with interp_fm in H.
        apply H.
      + autorewrite with interp_fm; intros.
        apply H.
  Qed.

  Fixpoint reindex_var {c c': ctx} {sort: sig.(sig_sorts)} (v: var c' sort) : var (app_ctx c c') sort :=
    match v in (var c' sort) return (var (app_ctx c c') sort) with
    | VHere ctx _ =>
      VHere (app_ctx c ctx) _
    | VThere ctx _ _ v' =>
      VThere (app_ctx c ctx) _ _ (reindex_var v')
    end.

  Equations reindex_tm {c c': ctx} {sort: sig.(sig_sorts)} (t: tm c' sort) : tm (app_ctx c c') sort := {
    reindex_tm (TVar _ _ v) := TVar _ _ (reindex_var v);
    reindex_tm (TFun _ _ _ f args') := TFun _ _ _ f (reindex_tms args')
  } where reindex_tms {c c':ctx} {sorts: list sig.(sig_sorts)} (ts: HList.t (tm c') sorts) : HList.t (tm (app_ctx c c')) sorts := {
    reindex_tms hnil := hnil;
    reindex_tms (t ::: ts) := reindex_tm t ::: reindex_tms ts
  }.

  Equations weaken_var {sort: sig.(sig_sorts)}
             {c1: ctx} (c2: ctx) (v: var c1 sort)
    : var (app_ctx c1 c2) sort :=
    { weaken_var CEmp v := v;
      weaken_var (CSnoc c2' sort') v := VThere _ _ _ (weaken_var c2' v) }.

  Equations weaken_tm (sort: sig.(sig_sorts))
             (c1: ctx) (c2: ctx) (t: tm c1 sort)
    : tm (app_ctx c1 c2) sort
    by struct t :=
    { weaken_tm _ _ c2 (TVar _ _ v) := TVar _ _ (weaken_var c2 v);
      weaken_tm _ _ c2 (TFun _ _ _ f args') :=
        TFun _ _ _ f (weaken_tms _ _ c2 args') }
  where weaken_tms (sorts: list sig.(sig_sorts))
       (c1: ctx) (c2: ctx) (ts: HList.t (tm c1) sorts)
        : HList.t (tm (app_ctx c1 c2)) sorts
    by struct ts :=
    { weaken_tms _ _ _ hnil := hnil;
      weaken_tms _ _ _ (t ::: ts) :=
        weaken_tm _ _ c2 t ::: weaken_tms _ _ c2 ts }.

  Lemma find_app_left:
    forall m c1 c2 (val1: valu m c1) (val2: valu m c2) t (v: var c1 t),
      find m (weaken_var c2 v) (app_valu val1 val2) =
      find m v val1.
  Proof.
    intros; dependent induction c2;
    autorewrite with weaken_var.
    - dependent destruction val2.
      now autorewrite with app_valu.
    - dependent destruction val2.
      autorewrite with app_valu; simpl.
      rewrite find_equation_2.
      apply IHc2.
  Qed.

  Lemma find_app_right:
    forall m c1 c2 (val1: valu m c1) (val2: valu m c2) t (v: var c2 t),
      find m (reindex_var v) (app_valu val1 val2) =
      find m v val2.
  Proof.
    intros; dependent induction c2.
    - dependent destruction v.
    - dependent destruction val2.
      autorewrite with app_valu.
      dependent destruction v; simpl;
      autorewrite with find; auto.
  Qed.

  Lemma interp_tm_reindex_tm:
    forall m c s (t: tm c s) (v: valu m c) c' (v': valu m c'),
      interp_tm m c s v t =
      interp_tm m (app_ctx c' c) s (app_valu v' v) (reindex_tm t).
  Proof.
    dependent induction t using tm_ind'; intros.
    - autorewrite with reindex_tm.
      autorewrite with interp_tm.
      now rewrite find_app_right.
    - autorewrite with reindex_tm.
      autorewrite with interp_tm.
      f_equal.
      clear srt.
      induction hl; auto.
      autorewrite with reindex_tm.
      autorewrite with interp_tm.
      f_equal.
      + apply H.
      + apply IHhl, H.
  Qed.

  Lemma interp_tm_weaken_tm:
    forall m c s (t: tm c s) (v: valu m c) c' (v': valu m c'),
      interp_tm m c s v t =
      interp_tm m (app_ctx c c') s (app_valu v v') (weaken_tm s c c' t).
  Proof.
    dependent induction t using tm_ind'; intros.
    - autorewrite with weaken_tm.
      autorewrite with interp_tm.
      now rewrite find_app_left.
    - autorewrite with weaken_tm.
      autorewrite with interp_tm.
      f_equal.
      clear srt.
      induction hl; auto.
      autorewrite with weaken_tm.
      autorewrite with interp_tm.
      f_equal.
      + apply H.
      + apply IHhl, H.
  Qed.

  Equations tm_cons {c s' s}
    (t: tm c s)
    : tm (CSnoc c s') s := {
    tm_cons (TVar _ _ v) := TVar _ _ (VThere _ _ _ v);
    tm_cons (TFun _ _ _ fn args') := TFun _ _ _ fn (tms_cons args')
  } where tms_cons {c s' s}
    (ts: HList.t (tm c) s)
    : HList.t (tm (CSnoc c s')) s := {
    tms_cons hnil := hnil;
    tms_cons (t ::: ts) := tm_cons t ::: tms_cons ts
  }.

  Lemma interp_tm_tm_cons:
    forall m c s (t: tm c s) (v: valu m c) s' val,
      interp_tm m c s v t =
      interp_tm m (CSnoc c s') s (VSnoc m s' c v val) (tm_cons t).
  Proof.
    dependent induction t using tm_ind'; intros.
    - autorewrite with tm_cons.
      autorewrite with interp_tm.
      reflexivity.
    - autorewrite with tm_cons.
      autorewrite with interp_tm.
      f_equal.
      clear srt.
      induction hl; auto.
      autorewrite with tm_cons.
      autorewrite with interp_tm.
      f_equal.
      + apply H.
      + apply IHhl, H.
  Qed.

  Inductive QFFm : forall c, (fm c) -> Prop := 
  | QFTrue : forall c, QFFm c (FTrue _)
  | QFFalse : forall c, QFFm c (FFalse _)
  | QFRel : forall c typs rel args, QFFm c (FRel c typs rel args)
  | QFEq : forall c s l r,  QFFm c (FEq _ s l r)
  | QFNeg : forall c i, QFFm c i -> QFFm _ (FNeg _ i)
  | QFOr : forall c l r, QFFm c l -> QFFm _ r -> QFFm _ (FOr _ l r)
  | QFFand : forall c l r, QFFm c l -> QFFm _ r -> QFFm _ (FAnd _ l r)
  | QFImpl : forall c l r, QFFm c l -> QFFm _ r -> QFFm _ (FImpl _ l r).


End FOL.

Arguments TVar {_ _ _}.
Arguments TFun _ {_ _ _} _ _.
Arguments FTrue {sig c}.
Arguments FFalse {sig c}.
Arguments FEq {_ _ _} _ _.
Arguments FRel {_ _} _ _.
Arguments FNeg {_} _.
Arguments FOr {_} _ _.
Arguments FAnd {_} _ _.
Arguments FForall {_ _} _.
Arguments FImpl {_ _} _ _.

Arguments interp_fm {_ _ _} _ _.
Arguments interp_tm {_ _ _ _} _ _.
Arguments interp_tms {_ _ _ _} _ _.

Arguments app_ctx {sig} c1 c2.
Arguments quantify {sig c0} c f.
Arguments quantify_all {sig} c f.
Arguments reindex_var {sig c c' sort} v.
Arguments reindex_tm {sig c c' sort} t.
Arguments reindex_tms {sig c c' sorts} ts.
Arguments weaken_var {sig sort c1} c2 v.
Arguments weaken_tm {sig sort c1} c2 t.



Register TVar as p4a.core.var.
Register TFun as p4a.core.fun.

Register VHere as p4a.core.vhere.
Register VThere as p4a.core.vthere.


Register FEq as p4a.core.eq.
Register FTrue as p4a.core.tt.
Register FFalse as p4a.core.ff.
Register FRel as p4a.core.rel.
Register FNeg as p4a.core.neg.
Register FOr as p4a.core.or.
Register FAnd as p4a.core.and.
Register FForall as p4a.core.forall.

Register FImpl as p4a.core.impl.

Register SLNil as p4a.core.cnil.
Register Snoc as p4a.core.csnoc.

Register HList.HNil as p4a.core.hnil.
Register HList.HCons as p4a.core.hcons.

Require Import Coq.Lists.List.

(* a functor view of FOL, mapping between different sets of sorts and function/relation symbols *)

Section FMap.
  Variable (sigA sigB: signature).
  Variable (mA: model sigA).
  Variable (mB: model sigB).

  Fixpoint fmap_arity {sigA sigB: signature} (fmap_srt : sigA.(sig_sorts) -> sigB.(sig_sorts)) (arr: arity sigA.(sig_sorts)) : arity sigB.(sig_sorts) :=
    match arr with 
    | nil => nil
    | s :: arrs => fmap_srt s :: fmap_arity fmap_srt arrs
    end.
  Record theory_functor {sigA sigB: signature} {mA: model sigA} {mB: model sigB} := {
   fmap_sorts : sigA.(sig_sorts) -> sigB.(sig_sorts);
   fmap_funs : forall arr srt, sigA.(sig_funs) arr srt  -> sigB.(sig_funs) (fmap_arity fmap_sorts arr) (fmap_sorts srt);
   fmap_rels : forall arr, sigA.(sig_rels) arr -> sigB.(sig_rels) (fmap_arity fmap_sorts arr);
   fmap_mv : forall srt, mod_sorts sigA mA srt -> mod_sorts sigB mB (fmap_sorts srt);
  }.

  Variable (a2b: @theory_functor sigA sigB mA mB).
  
  Fixpoint fmap_ctx (c: ctx sigA) : ctx sigB := 
    match c with 
    | SLNil _ => SLNil _
    | Snoc _ i x => Snoc _ (fmap_ctx i) (a2b.(fmap_sorts) x)
    end.

  Equations fmap_var {c srt} (v: var sigA c srt) : var sigB (fmap_ctx c) (a2b.(fmap_sorts) srt) :=
  { 
    fmap_var (VHere _ c s) := VHere _ _ _;
    fmap_var (VThere _ _ _ _ i) := VThere _ _ _ _ (fmap_var i)
  }.

  Equations fmap_valu {c} (v: valu sigA mA c) : valu sigB mB (fmap_ctx c) := 
    fmap_valu VEmp := VEmp _ _;
    fmap_valu (VSnoc _ _ i x) := VSnoc _ _ _ _ (fmap_valu i) (a2b.(fmap_mv) _ x).


  Variable (fmap_fun_arrs: forall c arr srt, 
    sig_funs sigA arr srt -> 
    HList.t (fun srt' : sig_sorts sigA => tm sigB (fmap_ctx c) (a2b.(fmap_sorts) srt')) arr ->
    HList.t (tm sigB (fmap_ctx c)) (fmap_arity (a2b.(fmap_sorts)) arr)
  ).
  
  Equations fmap_tm {c srt} (t: tm sigA c srt) : tm sigB (fmap_ctx c) (a2b.(fmap_sorts) srt) := 
  {
    fmap_tm (TVar v) := TVar (fmap_var v);
    fmap_tm (@TFun _ c arr srt f args) := 
      TFun _ (a2b.(fmap_funs) _ _ f) (fmap_fun_arrs _ _ _ f (fmap_tm_args args))
  }
  where fmap_tm_args {c arr} (args: HList.t (tm sigA c) arr) 
    : HList.t (fun srt' : sig_sorts sigA => tm sigB (fmap_ctx c) (a2b.(fmap_sorts) srt')) arr := 
  {
    fmap_tm_args hnil := hnil;
    fmap_tm_args (h ::: t) := (fmap_tm h) ::: (fmap_tm_args t)
  }.

  Variable (fmap_rel_arrs: forall c arr, 
    sig_rels sigA arr -> 
    HList.t (fun srt' : sig_sorts sigA => tm sigB (fmap_ctx c) (a2b.(fmap_sorts) srt')) arr ->
    HList.t (tm sigB (fmap_ctx c)) (fmap_arity a2b.(fmap_sorts) arr)
  ).

  Variable (fmap_fm_fforall_op : 
    forall c s, 
      fm sigB (fmap_ctx (Snoc _ c s)) -> 
      fm sigB (fmap_ctx (Snoc _ c s))
  ).

  Equations fmap_fm {c} (f: fm sigA c) : fm sigB (fmap_ctx c) :=
  {
    fmap_fm FTrue := FTrue;
    fmap_fm FFalse := FFalse;
    fmap_fm (FEq l r) := FEq (fmap_tm l) (fmap_tm r);
    fmap_fm (FRel r args') := FRel _ (a2b.(fmap_rels) _ r) (fmap_rel_arrs _ _ r (fmap_tm_args args'));
    fmap_fm (FNeg x) := FNeg _ (fmap_fm x);
    fmap_fm (FOr l r) := FOr _ (fmap_fm l) (fmap_fm r);
    fmap_fm (FAnd l r) := FAnd _ (fmap_fm l) (fmap_fm r);
    fmap_fm (FImpl l r) := FImpl (fmap_fm l) (fmap_fm r);
    fmap_fm (FForall s i) := 
      FForall _ (fmap_fm_fforall_op _ s (fmap_fm i))
  }.

  Record functor_wf := {
    interp_tm_inj:
    forall srt c (v: valu _ mA c) t t',
      interp_tm v t = interp_tm v t' <->
      interp_tm (fmap_valu v) (fmap_tm t) = interp_tm (fmap_valu v) (fmap_tm (c:=c) (srt:=srt) t');
    fmap_rel_equi:
      forall c v args r r_args,
        mod_rels sigA mA args r (interp_tms v r_args) <->
        mod_rels sigB mB (fmap_arity a2b.(fmap_sorts) args) (a2b.(fmap_rels) args r) (interp_tms (fmap_valu v) (fmap_rel_arrs c args r (fmap_tm_args r_args)));
    interp_fmap_forall_equi: 
      forall srt c v (f : fm sigA (Snoc _ c srt)),
        (forall vA,
          interp_fm (VSnoc sigB mB (a2b.(fmap_sorts) srt) (fmap_ctx c) (fmap_valu v) (a2b.(fmap_mv) srt vA)) (fmap_fm f)) <->
        (forall vB,
          interp_fm (VSnoc sigB mB (a2b.(fmap_sorts) srt) (fmap_ctx c) (fmap_valu v) vB) (fmap_fm_fforall_op _ srt (fmap_fm f)))
  }.

  Theorem fmap_corr (wf: functor_wf): 
    forall (c: ctx sigA) v f, 
      interp_fm v f <-> interp_fm (fmap_valu v) (fmap_fm (c:= c) f).
  Proof.
    inversion wf.
    intros.
    dependent induction f;
    autorewrite with fmap_fm;
    autorewrite with interp_fm;
    try erewrite IHf;
    try erewrite IHf1;
    try erewrite IHf2;
    try eapply iff_refl.
    - eapply interp_tm_inj0.
    - eapply fmap_rel_equi0.
    - fold fmap_ctx.
      setoid_rewrite IHf.
      setoid_rewrite fmap_valu_equation_2.
      eapply interp_fmap_forall_equi0.
  Qed.
End FMap.

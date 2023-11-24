From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import MirrorSolve.HLists.

Import HListNotations.

Set Universe Polymorphism.

Section PolySyntax.

Definition ty_ctx := nat.
Context {sig_sorts : nat -> Type}.

Inductive ty_valu {T: Type} : ty_ctx -> snoc_list T -> Type := 
| TVEmp : 
  ty_valu 0 SLNil
| TVSnoc : 
  forall {ctx sl}, 
    ty_valu ctx sl -> 
    forall t, 
      ty_valu (S ctx) (Snoc sl t).

Inductive ty_ctx_var: ty_ctx -> Type :=
| TCVHere:
  forall {ctx},
    ty_ctx_var (S ctx)
| TCVThere:
  forall {ctx},
    ty_ctx_var ctx ->
    ty_ctx_var (S ctx).

Inductive ty_expr_var : ty_ctx -> nat -> Type := 
| TEVAnon  : 
  forall {ctx},
    ty_ctx_var ctx -> 
    ty_expr_var ctx 0
| TEVNamed : 
  forall {ctx arity}, 
    sig_sorts arity ->  
    ty_expr_var ctx arity.

Inductive ty_expr (ctx: ty_ctx) : nat -> Type := 
| TEVar : 
  forall {arity}, 
    ty_expr_var ctx arity -> 
    ty_expr ctx arity
| TEApp : 
  forall {arity}, (* apply a type function *)
    ty_expr ctx (S arity) -> 
    ty_expr ctx 0 -> 
    ty_expr ctx arity.

Arguments TEVar {_ _} _.
Arguments TEApp {_ _} _ _.

Record signature: Type :=
  { sig_funs: forall ctx, list (ty_expr ctx 0) -> ty_expr ctx 0 -> Type;
    sig_rels: forall ctx, list (ty_expr ctx 0) -> Type }.

Definition ctx t_ctx := snoc_list (ty_expr t_ctx 0).

Inductive var: forall {t_ctx}, ctx t_ctx -> ty_expr t_ctx 0 -> Type := 
| VHere:
  forall {t_ctx} {c: ctx t_ctx} {e},
    var (Snoc c e) e
| VThere:
  forall {t_ctx} {c: ctx t_ctx} {s s'},
    var c s' ->
    var (Snoc c s) s'.
Derive Signature NoConfusion for var.

Context {sig: signature}.


(* A list of type expressions in an outer context, with same size as an inner context.
   The type indices are:
    type_params t_outer t_inner t_exprs
*)

Definition ty_params t_ctx_outer := @ty_valu (ty_expr t_ctx_outer 0).

Equations lookup_tp_var t_ctx_outer t_ctx_inner tys (tp: ty_params t_ctx_outer t_ctx_inner tys) (tc_var: ty_ctx_var t_ctx_inner) : ty_expr t_ctx_outer 0 := {
  lookup_tp_var _ _ _ (TVSnoc _ e) TCVHere := e; 
  lookup_tp_var _ _ _ (TVSnoc tv' _) (TCVThere tc_var') := 
    lookup_tp_var _ _ _ tv' tc_var'; 
}.

(* Local Obligation Tactic := idtac. *)
Equations apply_ty_args 
  t_ctx_inner t_ctx_outer t_args n
  (ty_args: ty_params t_ctx_outer t_ctx_inner t_args)
  (te_inner : ty_expr t_ctx_inner n) : ty_expr t_ctx_outer n by struct te_inner := {
  apply_ty_args _ t_ctx_outer _ _ tp (TEApp l r) := 
    TEApp (apply_ty_args _ _ _ _ _ l) (apply_ty_args _ _ _ _ _ r);
  apply_ty_args _ _ _ _ tp (TEVar (TEVNamed f)) := 
    TEVar (TEVNamed f);
  apply_ty_args _ _ _ _ tp (TEVar (TEVAnon v)) := 
    lookup_tp_var _ _ _ tp v;
}.

Inductive tm {t_ctx} : ctx t_ctx -> ty_expr t_ctx 0 -> Type :=
| TVar: 
  forall {c s},
    var c s ->
    tm c s
| TFun:
  forall {t_ctx' args ret} {t_args} {c: ctx t_ctx},
    sig.(sig_funs) t_ctx' args ret ->
    forall (ty_args : ty_params t_ctx t_ctx' t_args), (* type arguments *)
      HList.t (tm c) (List.map (apply_ty_args t_ctx' t_ctx t_args 0 ty_args) args) -> 
      tm c (apply_ty_args t_ctx' t_ctx t_args 0 ty_args ret). 

Derive Signature for tm.

Inductive fm {t_ctx} : ctx t_ctx -> Type :=
(* True and False *)
| FTrue: forall {c}, fm c
| FFalse: forall {c}, fm c
(* Equality *)
| FEq: 
  forall {c s},
    tm c s ->
    tm c s ->
    fm c
(* A relation (with arguments) *)
| FRel:
  forall {t_ctx' args} {t_args} {c: ctx t_ctx},
    sig.(sig_rels) t_ctx' args ->
    forall (ty_args : ty_params t_ctx t_ctx' t_args), (* type arguments *)
      HList.t (tm c) (List.map (apply_ty_args t_ctx' t_ctx t_args 0 ty_args) args) -> 
      fm c
(* Negation, disjunction, conjunction, and implication *)
| FNeg: forall {c}, fm c -> fm c
| FOr: forall {c}, fm c -> fm c -> fm c
| FAnd: forall {c}, fm c -> fm c -> fm c
| FImpl: forall {c}, fm c -> fm c -> fm c
| FBiImpl: forall {c}, fm c -> fm c -> fm c
(* Quantification *)
| FForall:
  forall {c} s,
    fm (Snoc c s) ->
    fm c
| FExists:
  forall {c} s,
    fm (Snoc c s) ->
    fm c.
Derive Signature for fm.

Inductive poly_fm : ty_ctx -> Type := 
| PFm : 
  forall {tc}, 
    fm (SLNil : ctx tc)  -> 
    poly_fm tc
| PForall : 
  forall {tc}, 
    poly_fm (S tc) -> 
    poly_fm tc.
End PolySyntax.


Arguments TEVar {_ _ _} _.
Arguments TEApp {_ _ _} _ _.

Section PolySemantics.

Fixpoint arity_ftor (n: nat) : Type := 
  match n with 
  | 0 => Type
  | (S n) => (Type -> arity_ftor n)
  end.

Context {sig_sorts : nat -> Type}.
Context {interp_sorts : forall n, sig_sorts n -> arity_ftor n}.
Context {sig: @signature sig_sorts}.

Set Transparent Obligations.

Equations lookup_tc_var {A} ctx (tys: snoc_list A) (tv: ty_valu ctx tys) (tc_var: ty_ctx_var ctx) : A := {
  lookup_tc_var _ _ (TVSnoc _ T) TCVHere := T; 
  lookup_tc_var _ _ (TVSnoc tv' _) (TCVThere tc_var') := lookup_tc_var _ _ tv' tc_var'; 
}.

Equations interp_te_var ctx (tys: snoc_list Type) (tv: ty_valu ctx tys) n (te_var: @ty_expr_var sig_sorts ctx n) : arity_ftor n := {
  interp_te_var _ _ tv _ (TEVAnon v) := 
    lookup_tc_var _ _ tv v;
  interp_te_var ctx _ _ n (TEVNamed f) := 
    interp_sorts _ f;
}.

Equations interp_te ctx (tys: snoc_list Type) (tv: ty_valu ctx tys) n (te: @ty_expr sig_sorts ctx n) : arity_ftor n := {
  interp_te _ _ tv n (TEVar v) := 
    interp_te_var _ _ tv n v;
  interp_te ctx tys tv _ (TEApp l r) := 
    let T := interp_te ctx tys tv _ r in 
      (interp_te ctx tys tv _ l) T;
}.

Equations apply_outer_params_tv
  t_ctx_inner t_ctx_outer t_args (tys_outer: snoc_list Type)
  (ty_args: @ty_params sig_sorts t_ctx_outer t_ctx_inner t_args)
  (tv_outer : ty_valu t_ctx_outer tys_outer) 
  : ty_valu t_ctx_inner (sl_map (interp_te _ _ tv_outer 0) t_args) 
    by struct ty_args := {
  apply_outer_params_tv _ _ _ _ TVEmp _ := TVEmp;
  apply_outer_params_tv _ _ _ _ (TVSnoc tp' _) _ := TVSnoc (apply_outer_params_tv _ _ _ _ tp' _) _;
}.

Local Obligation Tactic := intros.
Equations lookup_tvar_apply_eq {ctx t_ctx tys t_args tv} tp tvar :
  interp_te t_ctx tys tv 0 (@lookup_tp_var sig_sorts t_ctx ctx t_args tp tvar) =
  lookup_tc_var ctx (sl_map (interp_te t_ctx tys tv 0) t_args) (apply_outer_params_tv ctx t_ctx t_args tys tp tv) tvar
  by struct tvar := {
  lookup_tvar_apply_eq (TVSnoc _ _) TCVHere := eq_refl;
  lookup_tvar_apply_eq (TVSnoc _ _) (TCVThere _) := _;
}.
Next Obligation.
  autorewrite with lookup_tp_var.
  autorewrite with apply_outer_params_tv.
  simpl.
  autorewrite with lookup_tc_var.
  eapply lookup_tvar_apply_eq.
Defined.

Local Obligation Tactic := (unfold RelationClasses.complement, Equivalence.equiv; Tactics.program_simpl).

Lemma apply_outer_eq:
  forall n t_ctx t_ctx' tys t_args tp tv e, 
    interp_te t_ctx tys tv n (@apply_ty_args sig_sorts t_ctx' t_ctx t_args n tp e) 
    = 
    interp_te t_ctx' (sl_map (interp_te t_ctx tys tv 0) t_args) (apply_outer_params_tv t_ctx' t_ctx t_args tys tp tv) n e.
Proof.
induction e.
  - simpl.
    destruct t; autorewrite with apply_ty_args.
    + autorewrite with interp_te.
      autorewrite with interp_te_var.
      eapply lookup_tvar_apply_eq.
    + autorewrite with interp_te.
      autorewrite with interp_te_var.
      trivial.
  - autorewrite with apply_ty_args.
    unfold apply_ty_args_obligations_obligation_1, apply_ty_args_obligations_obligation_2, apply_ty_args_obligations_obligation_3, apply_ty_args_obligations_obligation_4.
    autorewrite with interp_te.
    simpl.
    erewrite IHe2.
    erewrite IHe1.
    trivial.
Defined.


Record interp_sig (sig: @signature sig_sorts) := {
  interp_funs: 
    forall t_ctx ctx args ret, 
      sig_funs sig t_ctx args ret -> 
      forall (tv: ty_valu t_ctx ctx), 
        HList.t (interp_te t_ctx ctx tv 0) args ->
        interp_te t_ctx ctx tv 0 ret;
  interp_rels: 
    forall t_ctx ctx args, 
      sig_rels sig t_ctx args -> 
      forall (tv: ty_valu t_ctx ctx), 
        HList.t (interp_te t_ctx ctx tv 0) args ->
        Prop;
}.

Context {model: interp_sig sig}.

Inductive valu {ty_ctx tys} (tv: ty_valu ty_ctx tys) : @ctx sig_sorts ty_ctx -> Type := 
| VEmp : 
  valu tv SLNil
| VSnoc : 
  forall {sl e}, 
    valu tv sl -> 
    interp_te ty_ctx tys tv 0 e ->
    valu tv (Snoc sl e).

Arguments VEmp {_ _ _}.
Arguments VSnoc {_ _ _ _ _} _ _.

Equations interp_var t_ctx tys (tv: ty_valu t_ctx tys) e_ctx e (env: valu tv e_ctx) (v: var e_ctx e) : interp_te t_ctx tys tv 0 e := {
  interp_var _ _ _ _ _ (VSnoc _ v) VHere := v;
  interp_var _ _ _ _ _ (VSnoc env _) (VThere vi) := interp_var _ _ _ _ _ env vi;
}.

Equations 
  interp_tm 
    t_ctx tys (tv: ty_valu t_ctx tys) e_ctx e 
    (env: valu tv e_ctx) 
    (t: tm (sig := sig) e_ctx e) 
  : interp_te t_ctx tys tv 0 e 
    by struct t 
  := {
  interp_tm _ _ _ _ _ env (TVar v) := 
    interp_var _ _ _ _ _ env v;
  interp_tm _ tys tv _ _ env (@TFun _ _ _ t_args _ f tp hargs) :=
    let inner := interp_tms _ _ tv _ _ env hargs in
    let swapped := HList.map_swap _ _ inner in 
    let trans_args := HList.map _ swapped in 
    let inner_v := 
      model.(interp_funs sig) _ (sl_map (interp_te _ _ tv 0) t_args) _ _ f (apply_outer_params_tv _ _ _ _ tp tv) trans_args in 
    eq_rect_r (fun (x: arity_ftor 0) => x) inner_v (apply_outer_eq _ _ _ _ _ _ _ _);
      (* interp_te_outer_params_apply _ inner_v; *)
      (* _; *)
} where 
  interp_tms 
    t_ctx ctx (tv: ty_valu t_ctx ctx) e_ctx tys
    (env: valu tv e_ctx)  
    (tms: HList.t 
      (fun (te : ty_expr t_ctx 0) => tm (sig := sig) e_ctx te) 
      tys
    ) 
  : HList.t (interp_te t_ctx ctx tv 0) tys by struct tms := {
interp_tms _ _ _ _ _ _ hnil := 
  hnil;
interp_tms _ _ _ _ env _ (t ::: ts) := 
  interp_tm _ _ _ _ _ _ t ::: interp_tms _ _ _ _ _ _ ts;
}.
Next Obligation.
erewrite apply_outer_eq in X.
apply X.
Defined.

Equations interp_fm t_ctx tys (tv: ty_valu t_ctx tys) e_ctx (env: valu tv e_ctx) (f: fm (sig := sig) e_ctx) : Prop := {
  interp_fm _ _ _ _ _ FTrue := True;
  interp_fm _ _ _ _ _ FFalse := False;
  interp_fm _ _ _ _ _ (FEq l r) := 
    (interp_tm _ _ _ _ _ _ l) = (interp_tm _ _ _ _ _ _ r);
  interp_fm _ _ tv _ env (@FRel _ _ t_args _ f tp hargs) :=
    let inner := interp_tms _ _ tv _ _ env hargs in
    let swapped := HList.map_swap _ _ inner in 
    let trans_args := HList.map _ swapped in 
      model.(interp_rels sig) _ (sl_map (interp_te _ _ tv 0) t_args) _ f (apply_outer_params_tv _ _ _ _ tp tv) trans_args;
  interp_fm _ _ _ _ _ (FAnd l r) := 
    interp_fm _ _ _ _ _ l /\ interp_fm _ _ _ _ _ r ;
  interp_fm _ _ _ _ _ (FOr l r) := 
    interp_fm _ _ _ _ _ l \/ interp_fm _ _ _ _ _ r ;
  interp_fm _ _ _ _ _ (FImpl l r) := 
    interp_fm _ _ _ _ _ l -> interp_fm _ _ _ _ _ r ;
  interp_fm _ _ _ _ _ (FBiImpl l r) := 
    interp_fm _ _ _ _ _ l <-> interp_fm _ _ _ _ _ r ;
  interp_fm _ _ _ _ _ (FNeg f) := 
    ~ interp_fm _ _ _ _ _ f ;
  interp_fm t_ctx tys tv _ env (FForall e f) := 
    forall (x: interp_te t_ctx tys tv 0 e), 
      interp_fm _ _ _ _ (VSnoc env x) f ;
  interp_fm t_ctx tys tv _ env (FExists e f) := 
    exists (x: interp_te t_ctx tys tv 0 e), 
      interp_fm _ _ _ _ (VSnoc env x) f ;
}.
Next Obligation.
erewrite apply_outer_eq in X.
apply X.
Defined.

Equations interp_pfm t_ctx (tys: snoc_list Type) (tv: ty_valu t_ctx tys) (pf: poly_fm (sig := sig) t_ctx) : Prop := {
  interp_pfm t_ctx tys tv (PFm f) := 
    interp_fm t_ctx tys tv _ VEmp f;
  interp_pfm t_ctx tys tv (PForall pf) := 
    forall (T: Type), 
      interp_pfm _ _ (TVSnoc _ T) pf;
}.

End PolySemantics.

Arguments VEmp {_ _ _ _ _}.
Arguments VSnoc {_ _ _ _ _ _ _} _ _.


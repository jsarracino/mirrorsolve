From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import MirrorSolve.HLists.

Import HListNotations.

Set Universe Polymorphism.

Section PolySyntax.

(* Definition ty_ctx := snoc_list Type. *)
Definition ty_ctx := nat.
Context (sig_sorts : nat -> Type).

Inductive ty_ctx_var: ty_ctx -> Type :=
| TCVHere:
  forall ctx,
    ty_ctx_var (S ctx)
| TCVThere:
  forall ctx,
    ty_ctx_var ctx ->
    ty_ctx_var (S ctx).

Inductive ty_expr_var : ty_ctx -> nat -> Type := 
| TEVAnon  : 
  forall ctx,
    ty_ctx_var ctx -> 
    ty_expr_var ctx 0
| TEVNamed : 
  forall ctx arity, 
    sig_sorts arity ->  
    ty_expr_var ctx arity.

Inductive ty_expr (ctx: ty_ctx) : nat -> Type := 
| TEVar : 
  forall arity, 
    ty_expr_var ctx arity -> 
    ty_expr ctx arity
| TEApp : 
  forall arity, (* apply a type function *)
    ty_expr ctx (S arity) -> 
    ty_expr ctx 0 -> 
    ty_expr ctx arity.

Record signature: Type :=
  { sig_funs: forall ctx, list (ty_expr ctx 0) -> ty_expr ctx 0 -> Type;
    sig_rels: forall ctx, list (ty_expr ctx 0) -> Type }.

Definition ctx t_ctx := snoc_list (ty_expr t_ctx 0).

Inductive var: forall t_ctx, ctx t_ctx -> ty_expr t_ctx 0 -> Type := 
| VHere:
  forall t_ctx (c: ctx t_ctx) e,
    var t_ctx (Snoc _ c e) e
| VThere:
  forall t_ctx (c: ctx t_ctx) s s',
    var t_ctx c s' ->
    var _ (Snoc _ c s) s'.
Derive Signature NoConfusion for var.

Context (sig: signature).

Inductive tm t_ctx : ctx t_ctx -> ty_expr t_ctx 0 -> Type :=
| TVar: 
  forall c s,
    var t_ctx c s ->
    tm t_ctx c s
| TFun:
  forall c args ret,
    sig.(sig_funs) t_ctx args ret ->
    HList.t (tm t_ctx c) args ->
    tm t_ctx c ret.
Derive Signature for tm.

Inductive fm t_ctx : ctx t_ctx -> Type :=
(* True and False *)
| FTrue: forall c, fm t_ctx c
| FFalse: forall c, fm t_ctx c
(* Equality *)
| FEq: 
  forall c s,
    tm t_ctx c s ->
    tm t_ctx c s ->
    fm t_ctx c
(* A relation (with arguments) *)
| FRel:
  forall c args,
    sig.(sig_rels) t_ctx args ->
    HList.t (tm t_ctx c) args ->
    fm t_ctx c 
(* Negation, disjunction, conjunction, and implication *)
| FNeg: forall c, fm t_ctx c -> fm t_ctx c
| FOr: forall c, fm t_ctx c -> fm t_ctx c -> fm t_ctx c
| FAnd: forall c, fm t_ctx c -> fm t_ctx c -> fm t_ctx c
| FImpl: forall c, fm t_ctx c -> fm t_ctx c -> fm t_ctx c
| FBiImpl: forall c, fm t_ctx c -> fm t_ctx c -> fm t_ctx c
(* Quantification *)
| FForall:
  forall c s,
    fm t_ctx (Snoc _ c s) ->
    fm t_ctx c
| FExists:
  forall c s,
    fm t_ctx (Snoc _ c s) ->
    fm t_ctx c.
Derive Signature for fm.

Inductive poly_fm : ty_ctx -> Type := 
| PFm : 
  forall tc, 
    fm tc (SLNil _ ) -> 
    poly_fm tc
| PForall : 
  forall tc, 
    poly_fm (S tc) -> 
    poly_fm tc.
End PolySyntax.

Section PolySemantics.

Context (sig_sorts : nat -> Type).

Fixpoint arity_ftor (n: nat) : Type := 
  match n with 
  | 0 => Type
  | (S n) => (Type -> arity_ftor n)
  end.

Context `(interp_sorts : forall n, sig_sorts n -> arity_ftor n).

Context `(sig: signature sig_sorts).

Inductive ty_valu : ty_ctx -> snoc_list Type -> Type := 
| TVEmp : 
  ty_valu 0 (SLNil _)
| TVSnoc : 
  forall ctx T sl, 
    ty_valu ctx sl -> 
    ty_valu (S ctx) (Snoc _ sl T).

Equations lookup_tc_var ctx tys (tv: ty_valu ctx tys) (tc_var: ty_ctx_var ctx) : Type := {
  lookup_tc_var _ _ (TVSnoc _ T _ _) (TCVHere _) := T; 
  lookup_tc_var _ _ (TVSnoc _ _ _ tv') (TCVThere _ tc_var') := lookup_tc_var _ _ tv' tc_var'; 
}.

Equations interp_te_var ctx tys (tv: ty_valu ctx tys) n (te_var: ty_expr_var sig_sorts ctx n) : arity_ftor n := {
  interp_te_var _ _ tv _ (TEVAnon _ v) := 
    lookup_tc_var _ _ tv v;
  interp_te_var ctx _ _ n (TEVNamed _ _ f) := 
    interp_sorts _ f;
}.

Equations interp_te ctx tys (tv: ty_valu ctx tys) n (te: ty_expr sig_sorts ctx n) : arity_ftor n := {
  interp_te _ _ tv n (TEVar _ v) := 
    interp_te_var _ _ tv n v;
  interp_te ctx tys tv _ (TEApp _ l r) := 
    let T := interp_te ctx tys tv _ r in 
      (interp_te ctx tys tv _ l) T;
}.

Record interp_sig (sig: signature sig_sorts) := {
  interp_funs: 
    forall t_ctx ctx args ret, 
      sig_funs sig_sorts sig t_ctx args ret -> 
      forall (tv: ty_valu t_ctx ctx), 
        HList.t (interp_te t_ctx ctx tv 0) args ->
        interp_te t_ctx ctx tv 0 ret;
  interp_rels: 
    forall t_ctx ctx args, 
      sig_rels sig_sorts sig t_ctx args -> 
      forall (tv: ty_valu t_ctx ctx), 
        HList.t (interp_te t_ctx ctx tv 0) args ->
        Prop;
}.

Context (model: interp_sig sig).

Inductive valu ty_ctx tys (tv: ty_valu ty_ctx tys) : ctx sig_sorts ty_ctx -> Type := 
| VEmp : 
  valu ty_ctx tys tv (SLNil _)
| VSnoc : 
  forall sl e, 
    valu ty_ctx tys tv sl -> 
    interp_te ty_ctx tys tv 0 e ->
    valu ty_ctx tys tv (Snoc _ sl e).

Equations interp_var t_ctx tys tv e_ctx e (env: valu t_ctx tys tv e_ctx) (v: var sig_sorts _ e_ctx e) : interp_te t_ctx tys tv 0 e := {
  interp_var _ _ _ _ _ (VSnoc _ _ _ v) (VHere _ _ _ ) := v;
  interp_var _ _ _ _ _ (VSnoc _ _ env _) (VThere _ _ _ _ vi) := interp_var _ _ _ _ _ env vi;
}.

(* Obligation Tactic := idtac. *)
Equations 
  interp_tm t_ctx tys tv e_ctx e (env: valu t_ctx tys tv e_ctx) (t: tm sig_sorts sig t_ctx e_ctx e) : interp_te t_ctx tys tv 0 e by struct t := {
  interp_tm _ _ _ _ _ env (TVar _ _ v) := 
    interp_var _ _ _ _ _ env v;
  interp_tm _ _ _ _ _ env (TFun _ _ _ _ _ _ f hargs) := 
    model.(interp_funs sig) _ _ _ _ f _ (interp_tms _ _ _ _ env _ hargs);
} where 
  interp_tms t_ctx ctx tv e_ctx (env: valu t_ctx ctx tv e_ctx) tys (tms: HList.t (tm sig_sorts sig t_ctx e_ctx) tys) : HList.t (interp_te t_ctx ctx tv 0) tys by struct tms := {
  interp_tms _ _ _ _ _ _ hnil := 
    hnil;
  interp_tms _ _ _ _ _ _ (t ::: ts) := 
    interp_tm _ _ _ _ _ _ t ::: interp_tms _ _ _ _ _ _ ts;
}.

Equations interp_fm t_ctx tys tv e_ctx (env: valu t_ctx tys tv e_ctx) (f: fm sig_sorts sig t_ctx e_ctx) : Prop := {
  interp_fm _ _ _ _ _ (FTrue _) := True;
  interp_fm _ _ _ _ _ (FFalse _) := False;
  interp_fm _ _ _ _ _ (FEq _ _ l r) := 
    (interp_tm _ _ _ _ _ _ l) = (interp_tm _ _ _ _ _ _ r);
  interp_fm _ _ _ _ _ (FRel _ _ _ _ _ f hargs) := 
    model.(interp_rels sig) _ _ _ f _ (interp_tms _ _ _ _ _ _ hargs);
  interp_fm _ _ _ _ _ (FAnd _ l r) := 
    interp_fm _ _ _ _ _ l /\ interp_fm _ _ _ _ _ r ;
  interp_fm _ _ _ _ _ (FOr _ l r) := 
    interp_fm _ _ _ _ _ l \/ interp_fm _ _ _ _ _ r ;
  interp_fm _ _ _ _ _ (FImpl _ l r) := 
    interp_fm _ _ _ _ _ l -> interp_fm _ _ _ _ _ r ;
  interp_fm _ _ _ _ _ (FBiImpl _ l r) := 
    interp_fm _ _ _ _ _ l <-> interp_fm _ _ _ _ _ r ;
  interp_fm _ _ _ _ _ (FNeg _ f) := 
    ~ interp_fm _ _ _ _ _ f ;
  interp_fm t_ctx tys tv _ env (FForall _ e f) := 
    forall (x: interp_te t_ctx tys tv 0 e), 
      interp_fm _ _ _ _ (VSnoc _ _ _ _ _ env x) f ;
  interp_fm t_ctx tys tv _ env (FExists _ e f) := 
    exists (x: interp_te t_ctx tys tv 0 e), 
      interp_fm _ _ _ _ (VSnoc _ _ _ _ _ env x) f ;
}.

Equations interp_pfm t_ctx tys (tv: ty_valu t_ctx tys) (pf: poly_fm sig_sorts sig t_ctx) : Prop := {
  interp_pfm t_ctx tys tv (PFm _ f) := 
    interp_fm t_ctx tys tv _ (VEmp _ _ _) f;
  interp_pfm t_ctx tys tv (PForall _ pf) := 
    forall (T: Type), 
      interp_pfm _ _ (TVSnoc _ T _ _) pf;
}.

End PolySemantics.
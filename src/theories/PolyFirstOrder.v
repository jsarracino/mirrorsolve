From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import MirrorSolve.HLists.

Import HListNotations.

Set Universe Polymorphism.

Section PolySyntax.

(* Definition ty_ctx := snoc_list Type. *)
Definition ty_ctx := nat.
Context (sig_sorts : nat -> Type).

Inductive ty_valu : ty_ctx -> snoc_list Type -> Type := 
| TVEmp : 
  ty_valu 0 (SLNil _)
| TVSnoc : 
  forall ctx T sl, 
    ty_valu ctx sl -> 
    ty_valu (S ctx) (Snoc _ sl T).

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

(* Definition infer_args_ty t_parent t_child c_parent c_child args args' (parent_args : HList.t (tm t_parent c_parent) args) : HList.t (tm t_child c_child) args'. Admitted. *)

(* Definition lift_return t_parent t_child c_parent c_child *)

Context (sig: signature).

(* TODO:
    add type variables here, 
    calculate return type from type variables and function signature,
    calculate type of argument variables from type variables and function signature

  e.g.

    (forall A B (a: A) (b: B), A * B) [X, Y] => 
    args = X, Y
    ret = X * Y
*)

Inductive ty_params t_ctx_outer : ty_ctx -> snoc_list (ty_expr t_ctx_outer 0) -> Type := 
| TPEmp : 
  ty_params t_ctx_outer 0 (SLNil _)
| TPSnoc : 
  forall ctx te sl, 
    ty_params t_ctx_outer ctx sl -> 
    ty_params t_ctx_outer (S ctx) (Snoc _ sl te).

(* Definition infer_ 

  ty_expr t_ctx_inner 0 -> 
  ty_args -> 

  ty_expr t_ctx_outer 0
*)

(* 

  append has function type 
    forall A,
      A -> A -> A

  

*)

(* True but not needed *)
Definition insert_closed t_ctx n (te: ty_expr 0 n) : ty_expr t_ctx n.
Admitted.

Equations lookup_tp_var t_ctx_outer t_ctx_inner tys (tp: ty_params t_ctx_outer t_ctx_inner tys) (tc_var: ty_ctx_var t_ctx_inner) : ty_expr t_ctx_outer 0 := {
  lookup_tp_var _ _ _ (TPSnoc _ e _ _) (TCVHere _) := 
    e; 
  lookup_tp_var _ _ _ (TPSnoc _ _ _ tv') (TCVThere _ tc_var') := 
    lookup_tp_var _ _ _ tv' tc_var'; 
}.

(* Local Obligation Tactic := idtac. *)
Equations apply_ty_args 
  t_ctx_inner t_ctx_outer t_args n
  (ty_args: ty_params t_ctx_outer t_ctx_inner t_args)
  (te_inner : ty_expr t_ctx_inner n) : ty_expr t_ctx_outer n by struct te_inner := {
  apply_ty_args _ t_ctx_outer _ _ tp (TEApp _ _ l r) := 
    TEApp _ _ (apply_ty_args _ _ _ _ _ l) (apply_ty_args _ _ _ _ _ r);
  apply_ty_args _ _ _ _ tp (TEVar _ _ (TEVNamed _ _ f)) := 
    TEVar _ _ (TEVNamed _ _ f);
  apply_ty_args _ _ _ _ tp (TEVar _ _ (TEVAnon _ v)) := 
    lookup_tp_var _ _ _ tp v;
}.

Inductive tm t_ctx : ctx t_ctx -> ty_expr t_ctx 0 -> Type :=
| TVar: 
  forall c s,
    var t_ctx c s ->
    tm t_ctx c s
| TFun:
  forall t_ctx' t_args c args ret,
    sig.(sig_funs) t_ctx' args ret ->
    forall (ty_args : ty_params t_ctx t_ctx' t_args), (* type arguments *)
      HList.t (fun te => tm t_ctx c (apply_ty_args _ _ _ _ ty_args te)) args -> 
      tm t_ctx c (apply_ty_args _ _ _ _ ty_args ret). 


    (* 
      append : forall A (a: list A) (a': list A), A

      @append B : forall (a: list B) (a': list B), B

      B (bs: list B)

      append bs bs = ...

      @append B bs bs
    
    *)
    (* append: demo_funs 1 [list_A; list_A] list_A 

      this is what we have defined right now: 

      append -> 
      [list_A; list_A] -> 
      tm ...

      in a polymorphic setting, what we actually want is:

      (fun A => append ) -> 
      X -> 
      [list_X; list_X] -> 
      tm ... a term in which X and list_X are defined
    *)


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



Set Transparent Obligations.

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

(* TODO: fix up interp_funs to handle type arguments. Need to consider how to adjust hargs, which is in the outer context, 
    to the context of the inner function, which expects its own hargs.
*)
Equations 
  interp_tm t_ctx tys tv e_ctx e (env: valu t_ctx tys tv e_ctx) (t: tm sig_sorts sig t_ctx e_ctx e) : interp_te t_ctx tys tv 0 e by struct t := {
  interp_tm _ _ _ _ _ env (TVar _ _ v) := 
    interp_var _ _ _ _ _ env v;
  interp_tm _ _ _ _ _ env (TFun _ _ _ _ _ f _ hargs) := 
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

Arguments TEApp {_ _ _} _ _.
Arguments TEVar {_ _ _} _.
Arguments TEVAnon {_ _} _.
Arguments TEVNamed {_ _ _} _.
Arguments TCVHere {_}.

Section PolyDemo.

Require Import Coq.Lists.List.

Import ListNotations.

Inductive demo_sorts : nat -> Type := 
| sort_list : demo_sorts 1
| sort_nat : demo_sorts 0.

Notation list_A := (TEApp
  (TEVar (TEVNamed sort_list)) 
  (TEVar (TEVAnon TCVHere))
).

Notation nat_ty := (TEVar (TEVNamed sort_nat)).

Inductive demo_funs : 
  forall ctx, list (ty_expr demo_sorts ctx 0) -> ty_expr demo_sorts ctx 0 -> Type := 
| demo_app : demo_funs 1 [list_A; list_A] list_A (* forall A, list A -> list A -> list A*)
| demo_len : demo_funs 1 [list_A] nat_ty (* forall A, list A -> nat *)
| demo_add : demo_funs 1 [nat_ty; nat_ty] nat_ty (* nat -> nat -> nat *)
.

Inductive demo_rels : 
  forall ctx, list (ty_expr demo_sorts ctx 0) -> Type := .

Definition demo_sig : signature demo_sorts := {|
  sig_funs := demo_funs;
  sig_rels := demo_rels;
|}.

Definition interp_demo_sorts : forall n, demo_sorts n -> arity_ftor n := fun n srt => 
  match srt with 
  | sort_list => list
  | sort_nat => nat
  end.

Equations 
  interp_demo_funs t_ctx ctx args ret (fn: demo_funs t_ctx args ret) tv (hargs: HList.t (interp_te demo_sorts interp_demo_sorts t_ctx ctx tv 0) args) : 
  interp_te demo_sorts interp_demo_sorts t_ctx ctx tv 0 ret := {
  interp_demo_funs _ _ _ _ demo_app _ (l ::: r ::: _) := List.app l r; 
  interp_demo_funs _ _ _ _ demo_len _ (x ::: _) := List.length x; 
  interp_demo_funs _ _ _ _ demo_add _ (l ::: r ::: _) := l + r; 
}.

Definition interp_demo_rels t_ctx ctx args (fn: demo_rels t_ctx args) tv (hargs: HList.t (interp_te demo_sorts interp_demo_sorts t_ctx ctx tv 0) args) : Prop := 
  match fn with end.

Program Definition demo_model : interp_sig demo_sorts interp_demo_sorts demo_sig := {| 
  interp_funs := interp_demo_funs;
  interp_rels := interp_demo_rels;
|}.

Arguments PFm {_ _ _} _.
Arguments PForall {_ _ _} _.
Arguments FTrue {_ _ _ _}.
Arguments FForall {_ _ _ _} _ _.
Arguments FEq {_ _ _ _ _} _ _.
Arguments TVar {_ _ _ _ _} _.
Arguments VHere {_ _ _ _}.
Arguments VThere {_ _ _ _ _} _.
Arguments TFun {_ _ _ _ _ _} _ _.

Notation t_xs := (TVar (VThere VHere)).
Notation t_ys := (TVar VHere).

Notation t_app args := (TFun (sig := demo_sig) demo_app args).
Notation t_len args := (TFun (sig := demo_sig) demo_len args).
Notation t_add args := (TFun (sig := demo_sig) demo_add args).

(* a polyfm version of app_len, i.e. 
  forall A (xs ys: list A), 
    length (xs ++ ys) = length xs + length ys *)
Example app_len_pf: 
  interp_pfm demo_sorts interp_demo_sorts demo_sig demo_model 0 (SLNil _) TVEmp
  ( PForall (PFm (
    FForall list_A (FForall list_A (
      FEq 
        (t_len (t_app (t_xs ::: t_ys ::: hnil) ::: hnil))
        (t_add (t_len (t_xs ::: hnil) ::: (t_len (t_ys ::: hnil)) ::: hnil))
    )))
  )).
Proof.
  vm_compute.
  intros.
  eapply List.app_length.
Qed.

End PolyDemo.
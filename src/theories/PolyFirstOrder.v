From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import MirrorSolve.HLists.

Import HListNotations.

Set Universe Polymorphism.

Section PolySyntax.

(* Definition ty_ctx := snoc_list Type. *)
Definition ty_ctx := nat.
Context (sig_sorts : nat -> Type).

Inductive ty_valu {T: Type} : ty_ctx -> snoc_list T -> Type := 
| TVEmp : 
  ty_valu 0 SLNil
| TVSnoc : 
  forall ctx t sl, 
    ty_valu ctx sl -> 
    ty_valu (S ctx) (Snoc sl t).

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
    var t_ctx (Snoc c e) e
| VThere:
  forall t_ctx (c: ctx t_ctx) s s',
    var t_ctx c s' ->
    var _ (Snoc c s) s'.
Derive Signature NoConfusion for var.

Context (sig: signature).


(* A list of type expressions in an outer context, with same size as an inner context.
   The type indices are:
    type_params t_outer t_inner t_exprs
*)

Definition ty_params t_ctx_outer := @ty_valu (ty_expr t_ctx_outer 0).

Equations lookup_tp_var t_ctx_outer t_ctx_inner tys (tp: ty_params t_ctx_outer t_ctx_inner tys) (tc_var: ty_ctx_var t_ctx_inner) : ty_expr t_ctx_outer 0 := {
  lookup_tp_var _ _ _ (TVSnoc _ e _ _) (TCVHere _) := 
    e; 
  lookup_tp_var _ _ _ (TVSnoc _ _ _ tv') (TCVThere _ tc_var') := 
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
      HList.t (tm t_ctx c) (List.map (apply_ty_args t_ctx' t_ctx t_args 0 ty_args) args) -> 
      tm t_ctx c (apply_ty_args t_ctx' t_ctx t_args 0 ty_args ret). 

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
  forall t_ctx' t_args c args,
    sig.(sig_rels) t_ctx' args ->
    forall (ty_args : ty_params t_ctx t_ctx' t_args), (* type arguments *)
      HList.t (tm t_ctx c) (List.map (apply_ty_args t_ctx' t_ctx t_args 0 ty_args) args) -> 
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
    fm t_ctx (Snoc c s) ->
    fm t_ctx c
| FExists:
  forall c s,
    fm t_ctx (Snoc c s) ->
    fm t_ctx c.
Derive Signature for fm.

Inductive poly_fm : ty_ctx -> Type := 
| PFm : 
  forall tc, 
    fm tc SLNil -> 
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

Equations lookup_tc_var {A} ctx (tys: snoc_list A) (tv: ty_valu ctx tys) (tc_var: ty_ctx_var ctx) : A := {
  lookup_tc_var _ _ (TVSnoc _ T _ _) (TCVHere _) := T; 
  lookup_tc_var _ _ (TVSnoc _ _ _ tv') (TCVThere _ tc_var') := lookup_tc_var _ _ tv' tc_var'; 
}.

Equations interp_te_var ctx (tys: snoc_list Type) (tv: ty_valu ctx tys) n (te_var: ty_expr_var sig_sorts ctx n) : arity_ftor n := {
  interp_te_var _ _ tv _ (TEVAnon _ v) := 
    lookup_tc_var _ _ tv v;
  interp_te_var ctx _ _ n (TEVNamed _ _ f) := 
    interp_sorts _ f;
}.

Equations interp_te ctx (tys: snoc_list Type) (tv: ty_valu ctx tys) n (te: ty_expr sig_sorts ctx n) : arity_ftor n := {
  interp_te _ _ tv n (TEVar _ v) := 
    interp_te_var _ _ tv n v;
  interp_te ctx tys tv _ (TEApp _ l r) := 
    let T := interp_te ctx tys tv _ r in 
      (interp_te ctx tys tv _ l) T;
}.

Equations apply_outer_params_tv
  t_ctx_inner t_ctx_outer t_args (tys_outer: snoc_list Type)
  (ty_args: ty_params sig_sorts t_ctx_outer t_ctx_inner t_args)
  (tv_outer : ty_valu t_ctx_outer tys_outer) 
  : ty_valu t_ctx_inner (sl_map (interp_te _ _ tv_outer 0) t_args) 
    by struct ty_args := {
  apply_outer_params_tv _ _ _ _ TVEmp _ := TVEmp;
  apply_outer_params_tv _ _ _ _ (TVSnoc _ e _ tp') _ := TVSnoc _ _ _ (apply_outer_params_tv _ _ _ _ tp' _);
}.

Local Obligation Tactic := intros.
Equations lookup_tvar_apply_eq {ctx t_ctx tys t_args tv} tp tvar :
  interp_te t_ctx tys tv 0 (lookup_tp_var sig_sorts t_ctx ctx t_args tp tvar) =
  lookup_tc_var ctx (sl_map (interp_te t_ctx tys tv 0) t_args) (apply_outer_params_tv ctx t_ctx t_args tys tp tv) tvar
  by struct tvar := {
  lookup_tvar_apply_eq (TVSnoc _ _ _ _) (TCVHere _) := eq_refl;
  lookup_tvar_apply_eq (TVSnoc _ _ _ _) (TCVThere _ _) := _;
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
    interp_te t_ctx tys tv n (apply_ty_args sig_sorts t_ctx' t_ctx t_args n tp e) 
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
  valu ty_ctx tys tv SLNil
| VSnoc : 
  forall sl e, 
    valu ty_ctx tys tv sl -> 
    interp_te ty_ctx tys tv 0 e ->
    valu ty_ctx tys tv (Snoc sl e).

Equations interp_var t_ctx tys tv e_ctx e (env: valu t_ctx tys tv e_ctx) (v: var sig_sorts _ e_ctx e) : interp_te t_ctx tys tv 0 e := {
  interp_var _ _ _ _ _ (VSnoc _ _ _ v) (VHere _ _ _ ) := v;
  interp_var _ _ _ _ _ (VSnoc _ _ env _) (VThere _ _ _ _ vi) := interp_var _ _ _ _ _ env vi;
}.

Set Transparent Obligations.
(* Obligation Tactic := intros. *)
Equations 
  interp_tm 
    t_ctx tys tv e_ctx e 
    (env: valu t_ctx tys tv e_ctx) 
    (t: tm sig_sorts sig t_ctx e_ctx e) 
  : interp_te t_ctx tys tv 0 e 
    by struct t 
  := {
  interp_tm _ _ _ _ _ env (TVar _ _ v) := 
    interp_var _ _ _ _ _ env v;
  interp_tm _ tys tv _ _ env (TFun _ t_args _ _ _ f tp hargs) :=
    let inner := interp_tms _ _ tv _ env _ hargs in
    let swapped := HList.map_swap _ _ inner in 
    let trans_args := HList.map _ swapped in 
    let inner_v := 
      model.(interp_funs sig) _ (sl_map (interp_te _ _ tv 0) t_args) _ _ f (apply_outer_params_tv _ _ _ _ tp tv) trans_args in 
    eq_rect_r (fun (x: arity_ftor 0) => x) inner_v (apply_outer_eq _ _ _ _ _ _ _ _);
      (* interp_te_outer_params_apply _ inner_v; *)
      (* _; *)
} where 
  interp_tms 
    t_ctx ctx tv e_ctx 
    (env: valu t_ctx ctx tv e_ctx) tys 
    (tms: HList.t 
      (fun (te : ty_expr sig_sorts t_ctx 0) => 
        tm sig_sorts sig t_ctx e_ctx te) 
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

Equations interp_fm t_ctx tys tv e_ctx (env: valu t_ctx tys tv e_ctx) (f: fm sig_sorts sig t_ctx e_ctx) : Prop := {
  interp_fm _ _ _ _ _ (FTrue _) := True;
  interp_fm _ _ _ _ _ (FFalse _) := False;
  interp_fm _ _ _ _ _ (FEq _ _ l r) := 
    (interp_tm _ _ _ _ _ _ l) = (interp_tm _ _ _ _ _ _ r);
  interp_fm _ _ tv _ env (FRel _ t_args _ _ f tp hargs) :=
    let inner := interp_tms _ _ tv _ env _ hargs in
    let swapped := HList.map_swap _ _ inner in 
    let trans_args := HList.map _ swapped in 
      model.(interp_rels sig) _ (sl_map (interp_te _ _ tv 0) t_args) _ f (apply_outer_params_tv _ _ _ _ tp tv) trans_args;
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
Next Obligation.
erewrite apply_outer_eq in X.
apply X.
Defined.

Equations interp_pfm t_ctx (tys: snoc_list Type) (tv: ty_valu t_ctx tys) (pf: poly_fm sig_sorts sig t_ctx) : Prop := {
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

Arguments PFm {_ _ _} _.
Arguments PForall {_ _ _} _.
Arguments FTrue {_ _ _ _}.
Arguments FForall {_ _ _ _} _ _.
Arguments FEq {_ _ _ _ _} _ _.
Arguments TVar {_ _ _ _ _} _.
Arguments VHere {_ _ _ _}.
Arguments VThere {_ _ _ _ _} _.
Arguments TFun {_ _ _ _ _ _ _ _} _ _ _.


Section PolyDemo.

Require Import Coq.Lists.List.

Import ListNotations.

Inductive demo_sorts : nat -> Type := 
| sort_list : demo_sorts 1
| sort_nat : demo_sorts 0.

Notation loc_A := (TEVar (TEVAnon TCVHere)).

Notation list_A := (TEApp
  (TEVar (TEVNamed sort_list)) 
  loc_A
).

Notation nat_ty := (TEVar (TEVNamed sort_nat)).

Inductive demo_funs : 
  forall ctx, list (ty_expr demo_sorts ctx 0) -> ty_expr demo_sorts ctx 0 -> Type := 
| demo_app : demo_funs 1 [list_A; list_A] list_A (* forall A, list A -> list A -> list A*)
| demo_len : demo_funs 1 [list_A] nat_ty (* forall A, list A -> nat *)
| demo_add : demo_funs 0 [nat_ty; nat_ty] nat_ty (* nat -> nat -> nat *)
| demo_zero : demo_funs 0 [] nat_ty
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
  interp_demo_funs _ _ _ _ demo_zero _ _ := 0; 
}.

Definition interp_demo_rels t_ctx ctx args (fn: demo_rels t_ctx args) tv (hargs: HList.t (interp_te demo_sorts interp_demo_sorts t_ctx ctx tv 0) args) : Prop := 
  match fn with end.

Program Definition demo_model : interp_sig demo_sorts interp_demo_sorts demo_sig := {| 
  interp_funs := interp_demo_funs;
  interp_rels := interp_demo_rels;
|}.




Notation t_xs := (TVar (VThere VHere)).
Notation t_ys := (TVar VHere).

Notation t_app ty_args args := (TFun (sig := demo_sig) demo_app ty_args args).
Notation t_len ty_args args := (TFun (sig := demo_sig) demo_len ty_args args).
Notation t_add args := (TFun (sig := demo_sig) demo_add TVEmp args).
Notation t_zero := (TFun (sig := demo_sig) demo_zero TVEmp hnil).

Program Definition app_len_pf_syntax: 
  poly_fm demo_sorts demo_sig 0 :=  PForall (PFm (
    FForall list_A (FForall list_A (
      FEq 
        (t_len _ ((t_app _ (t_xs ::: t_ys ::: hnil)) ::: hnil))
        (t_add ((t_len (TVSnoc _ loc_A _ TVEmp) (t_xs ::: hnil)) ::: (t_len _ (t_ys ::: hnil)) ::: hnil))
    ))
  )).

Example app_len_pf: 
  interp_pfm demo_sorts interp_demo_sorts demo_sig demo_model 0 SLNil TVEmp app_len_pf_syntax.
Proof.
  (* this short proof works as well: *)
  (* 
  vm_compute.
  intros.
  eapply List.app_length. 
  *)
  unfold app_len_pf_syntax.
  autorewrite with interp_pfm.
  unfold interp_pfm_obligations_obligation_1, interp_pfm_obligations_obligation_2.
  intros.
  autorewrite with interp_pfm.
  autorewrite with interp_fm.
  intros.
  vm_compute in x.
  autorewrite with interp_fm.
  intros.
  vm_compute in x0.
  set (t := apply_ty_args _ _ _ _ _ _ _).
  vm_compute in t.
  subst t.
  autorewrite with interp_fm.
  unfold interp_fm_obligations_obligation_1, interp_fm_obligations_obligation_2, interp_fm_obligations_obligation_3, interp_fm_obligations_obligation_4.
  set (t := apply_ty_args _ _ _ _ _ _ _);
  vm_compute in t;
  subst t.

  set (l := interp_tm _ _ _ _ _ _ _ _ _ _ _).
  set (r := interp_tm _ _ _ _ _ _ _ _ _ _ _).
  vm_compute in l.
  vm_compute in r.
  eapply List.app_length.
Qed.

(* Print Assumptions app_len_pf.  *)

End PolyDemo.

Section GenericTheory.

Variable generic_inner_sorts: nat -> Type.

Inductive generic_sorts: nat -> Type :=
| generic_arrow : generic_sorts 2
| generic_inner: forall n, generic_inner_sorts n -> generic_sorts n.

Notation loc_A := (TEVar (TEVAnon TCVHere)).
Notation loc_B := (TEVar (TEVAnon (TCVThere _ TCVHere))).

Notation arrow_A_B := (TEApp (TEApp (TEVar (TEVNamed generic_arrow)) loc_A) loc_B).

Import ListNotations.

Inductive generic_funs:
  forall ctx, list (ty_expr generic_sorts ctx 0) -> ty_expr generic_sorts ctx 0 -> Type :=
| generic_eval : generic_funs 2 [arrow_A_B; loc_A] loc_B (* forall A B, arrow A B -> A -> B*)
.

Inductive generic_rels:
  forall ctx, list (ty_expr generic_sorts ctx 0) -> Type := .

Definition generic_sig: signature generic_sorts := {|
  sig_funs := generic_funs;
  sig_rels := generic_rels;
|}.

Variable interp_generic_inner_sorts : forall n (sort: generic_inner_sorts n), arity_ftor n.

Equations interp_generic_sorts n (sort: generic_sorts n) : arity_ftor n := {
    interp_generic_sorts _ generic_arrow := fun A B => A -> B;
    interp_generic_sorts n (generic_inner n inner_sort) := interp_generic_inner_sorts n inner_sort
}.

Equations
  interp_generic_funs t_ctx ctx args ret (fn: generic_funs t_ctx args ret)
    tv (hargs: HList.t (interp_te generic_sorts interp_generic_sorts t_ctx ctx tv 0) args) :
  interp_te generic_sorts interp_generic_sorts t_ctx ctx tv 0 ret := {
  interp_generic_funs _ _ _ _ generic_eval _ (f ::: arg ::: _) := f arg;
}.

Definition interp_generic_rels t_ctx ctx args (rel: generic_rels t_ctx args) tv (hargs: HList.t (interp_te generic_sorts interp_generic_sorts t_ctx ctx tv 0) args) : Prop :=
  match rel with end.

Program Definition generic_model : interp_sig generic_sorts interp_generic_sorts generic_sig := {|
  interp_funs := interp_generic_funs;
  interp_rels := interp_generic_rels;
|}.

End GenericTheory.

Section GenericDemo.

Inductive generic_inner_sorts : nat -> Type :=
| inner_sort_list : generic_inner_sorts 1
| inner_sort_nat : generic_inner_sorts 0.

Notation te_arrow A B := (TEApp (TEApp (TEVar (TEVNamed (generic_arrow generic_inner_sorts))) A) B).
Notation loc_A := (TEVar (TEVAnon TCVHere)).
Notation list_A := (TEApp (TEVar (TEVNamed (generic_inner _ _ inner_sort_list))) loc_A).
Notation nat' := (TEVar (TEVNamed (generic_inner _ _ inner_sort_nat))).
Notation len_A := (te_arrow list_A nat').
Notation app_A := (te_arrow list_A (te_arrow list_A list_A)).
Notation cons_A := (te_arrow list_A (te_arrow loc_A list_A)).
Notation add' := (te_arrow nat' (te_arrow nat' nat')).
Notation t_eval ty_args args := (TFun (sig := generic_sig generic_inner_sorts) (generic_eval _) ty_args args).
Notation t_len_A arg := (t_eval (TVSnoc _ list_A _ (TVSnoc _ nat' _ TVEmp))
                                 (TVar (VThere (VThere (VThere (VThere VHere)))) ::: arg ::: hnil)).
Notation t_app_A x y := (t_eval (TVSnoc _ list_A _ (TVSnoc _ list_A _ TVEmp))
                              (t_eval (TVSnoc _ list_A _ (TVSnoc _ (te_arrow list_A list_A) _ TVEmp))
                              (TVar (VThere (VThere (VThere VHere))) ::: x ::: hnil) ::: y ::: hnil)).
Notation t_add' x y := (t_eval (TVSnoc _ nat' _ (TVSnoc _ nat' _ TVEmp))
                              (t_eval (TVSnoc _ nat' _ (TVSnoc _ (te_arrow nat' nat') _ TVEmp))
                              (TVar (VThere (VThere VHere)) ::: x ::: hnil) ::: y ::: hnil)).

Definition generic_test:
  poly_fm (generic_sorts generic_inner_sorts) (generic_sig generic_inner_sorts) 0 :=
  PForall (PFm (
    FForall len_A (
    FForall app_A (
    FForall add' (
    FForall list_A (
    FForall list_A (
      FEq
        (t_len_A (t_app_A (TVar VHere) (TVar (VThere VHere))))
        (t_add' (t_len_A (TVar VHere)) (t_len_A (TVar VHere)))
    )))))
  )).

Definition interp_generic_sorts_inner : forall n, generic_inner_sorts n -> arity_ftor n := fun n srt =>
  match srt with
  | inner_sort_list => list
  | inner_sort_nat => nat
  end.

Example app_len_generic:
    interp_pfm (generic_sorts generic_inner_sorts) (interp_generic_sorts generic_inner_sorts interp_generic_sorts_inner) (generic_sig generic_inner_sorts) (generic_model generic_inner_sorts interp_generic_sorts_inner) 0 SLNil TVEmp generic_test.
Proof.
  vm_compute.
Abort.

End GenericDemo.

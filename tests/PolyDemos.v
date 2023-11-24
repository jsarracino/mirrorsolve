From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import MirrorSolve.HLists.

Require Import MirrorSolve.PolyFirstOrder.

Import HListNotations.

Set Universe Polymorphism.



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
Notation cons_A := (te_arrow loc_A (te_arrow list_A list_A)).
Notation add' := (te_arrow nat' (te_arrow nat' nat')).
Notation t_eval ty_args args := (TFun (sig := generic_sig generic_inner_sorts) (generic_eval _) ty_args args).
Notation t_len_A arg := (t_eval (TVSnoc _ list_A _ (TVSnoc _ nat' _ TVEmp))
                                 (TVar (VThere (VThere (VThere (VThere (VThere VHere))))) ::: arg ::: hnil)).
Notation t_app_A x y := (t_eval (TVSnoc _ list_A _ (TVSnoc _ list_A _ TVEmp))
                              (t_eval (TVSnoc _ list_A _ (TVSnoc _ (te_arrow list_A list_A) _ TVEmp))
                              (TVar (VThere (VThere (VThere (VThere (VThere VHere))))) ::: x ::: hnil) ::: y ::: hnil)).
Notation t_app_A' x y := (t_eval (TVSnoc _ list_A _ (TVSnoc _ list_A _ TVEmp))
                              (t_eval (TVSnoc _ list_A _ (TVSnoc _ (te_arrow list_A list_A) _ TVEmp))
                              (TVar (VThere (VThere (VThere (VThere VHere)))) ::: x ::: hnil) ::: y ::: hnil)).
Notation t_cons_A a x := (t_eval (TVSnoc _ list_A _ (TVSnoc _ list_A _ TVEmp))
                              (t_eval (TVSnoc _ loc_A _ (TVSnoc _ (te_arrow list_A list_A) _ TVEmp))
                              (TVar (VThere (VThere (VThere (VThere VHere)))) ::: a ::: hnil) ::: x ::: hnil)).
Notation t_add' x y := (t_eval (TVSnoc _ nat' _ (TVSnoc _ nat' _ TVEmp))
                              (t_eval (TVSnoc _ nat' _ (TVSnoc _ (te_arrow nat' nat') _ TVEmp))
                              (TVar (VThere (VThere VHere)) ::: x ::: hnil) ::: y ::: hnil)).

Check FForall add' (
    FImpl _ _ _ _
        (
        FForall loc_A (
        FForall list_A (
        FForall list_A (
          FEq
            (t_app_A (t_cons_A (TVar (VThere (VThere VHere))) (TVar (VThere VHere))) (TVar VHere))
            (t_cons_A (TVar (VThere (VThere VHere))) (t_app_A (TVar (VThere VHere)) (TVar VHere)))
        ))))
        (FForall list_A (
        FForall list_A (
          FEq
            (t_len_A (t_app_A' (TVar VHere) (TVar (VThere VHere))))
            (t_add' (t_len_A (TVar VHere)) (t_len_A (TVar (VThere VHere))))
        )))
    ).

Definition generic_test:
  poly_fm (generic_sorts generic_inner_sorts) (generic_sig generic_inner_sorts) 0 :=
  PForall (PFm (
    FForall len_A (
    FForall app_A (
    FForall cons_A (
    FForall add' (
    FImpl _ _ _ _
        (
        FForall loc_A (
    FForall list_A (
    FForall list_A (
      FEq
            (t_app_A (t_cons_A (TVar (VThere (VThere VHere))) (TVar (VThere VHere))) (TVar VHere))
            (t_cons_A (TVar (VThere (VThere VHere))) (t_app_A (TVar (VThere VHere)) (TVar VHere)))
        ))))
        (FForall list_A (
        FForall list_A (
          FEq
            (t_len_A (t_app_A' (TVar VHere) (TVar (VThere VHere))))
            (t_add' (t_len_A (TVar VHere)) (t_len_A (TVar (VThere VHere))))
        )))
    )))
  ))).

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

Section ParametrizedTheory.

Open Scope type_scope.

Variable parametrized_inner_sorts: nat -> Type.

Inductive parametrized_sorts: nat -> Type :=
| parametrized_arrow : parametrized_sorts 2
| parametrized_inner: forall n, parametrized_inner_sorts n -> parametrized_sorts n.

Definition parametrized_manifest :=
    list {ctx & list (ty_expr parametrized_sorts ctx 0) *
                ty_expr parametrized_sorts ctx 0}.

Inductive parametrized_funs_open:
    parametrized_manifest ->
    forall ctx,
    list (ty_expr parametrized_sorts ctx 0) ->
    ty_expr parametrized_sorts ctx 0 ->
    Type
:=
| PFunHere:
    forall ctx
           tail
           (args: list (ty_expr parametrized_sorts ctx 0))
           (ret: ty_expr parametrized_sorts ctx 0),
        parametrized_funs_open (existT _ ctx (args, ret) :: tail) ctx args ret
| PFunThere:
    forall ctx
           head
           tail
           (args: list (ty_expr parametrized_sorts ctx 0))
           (ret: ty_expr parametrized_sorts ctx 0),
        parametrized_funs_open tail ctx args ret ->
        parametrized_funs_open (head :: tail) ctx args ret
.

Variable parametrized_inner_funcs: parametrized_manifest.

Definition parametrized_funs := parametrized_funs_open parametrized_inner_funcs.

Inductive parametrized_rels:
  forall ctx, list (ty_expr parametrized_sorts ctx 0) -> Type := .

Definition parametrized_sig: signature parametrized_sorts := {|
  sig_funs := parametrized_funs;
  sig_rels := parametrized_rels;
|}.

Variable interp_parametrized_inner_sorts : forall n (sort: parametrized_inner_sorts n), arity_ftor n.

Equations interp_parametrized_sorts n (sort: parametrized_sorts n) : arity_ftor n := {
    interp_parametrized_sorts _ parametrized_arrow := fun A B => A -> B;
    interp_parametrized_sorts n (parametrized_inner n inner_sort) := interp_parametrized_inner_sorts n inner_sort
}.

End ParametrizedTheory.


Section ConstantTypesAbstractedTheory.

Variable inner_sorts: nat -> Type.

Variable constant_sorts: Type.

Inductive abstract_sorts: nat -> Type :=
| abstract_constant : constant_sorts -> abstract_sorts 0
| abstract_inner_sort: forall n, inner_sorts n -> abstract_sorts n.

Variable inner_funs:
  forall ctx,
    list (ty_expr inner_sorts ctx 0) ->
    ty_expr inner_sorts ctx 0 ->
    Type
.

Equations abstract_ty_expr_var
  {n ctx}
  (var: ty_expr_var inner_sorts ctx n)
:
  ty_expr_var abstract_sorts ctx n
:= {
  abstract_ty_expr_var (TEVAnon var) :=
    TEVAnon var;
  abstract_ty_expr_var (TEVNamed name) :=
    TEVNamed (abstract_inner_sort _ name);
}.

Equations abstract_ty_expr
  {n ctx}
  (var: ty_expr inner_sorts ctx n)
:
  ty_expr abstract_sorts ctx n
:= {
  abstract_ty_expr (TEVar var) :=
    TEVar (abstract_ty_expr_var var);
  abstract_ty_expr (TEApp func arg) :=
    TEApp (abstract_ty_expr func)
          (abstract_ty_expr arg);
}.

Inductive abstract_funs:
  forall ctx,
    list (ty_expr abstract_sorts ctx 0) ->
    ty_expr abstract_sorts ctx 0 ->
    Type
:=
| abstract_inner_fun:
    forall ctx args ret,
      inner_funs ctx args ret ->
      abstract_funs ctx (map abstract_ty_expr args)
                        (abstract_ty_expr ret)
.

Variable inner_rels:
  forall ctx,
    list (ty_expr inner_sorts ctx 0) ->
    Type
.

Inductive abstract_rels:
  forall ctx,
    list (ty_expr abstract_sorts ctx 0) ->
    Type
:=
| abstract_inner_rel:
    forall ctx args,
      inner_rels ctx args ->
      abstract_rels ctx (map abstract_ty_expr args)
.

Definition abstract_sig: signature abstract_sorts := {|
  sig_funs := abstract_funs;
  sig_rels := abstract_rels;
|}.

Variable interp_inner_sorts: forall n (sort: inner_sorts n), arity_ftor n.
Variable interp_constants: constant_sorts -> Type.

Equations interp_abstract_sorts n (sort: abstract_sorts n) : arity_ftor n := {
  interp_abstract_sorts _ (abstract_inner_sort n inner_sort) := interp_inner_sorts n inner_sort;
  interp_abstract_sorts _ (abstract_constant constant) := interp_constants constant;
}.

Variable interp_inner_funs:
  forall t_ctx ctx args ret (fn: inner_funs t_ctx args ret) tv
    (hargs: HList.t (interp_te inner_sorts interp_inner_sorts t_ctx ctx tv 0) args),
    interp_te inner_sorts interp_inner_sorts t_ctx ctx tv 0 ret
.

Equations concretize_interp_te_var 
  t_ctx ctx tv te_var 
  (val: interp_te_var abstract_sorts interp_abstract_sorts ctx t_ctx tv 0 (abstract_ty_expr_var te_var)) 
: interp_te_var inner_sorts interp_inner_sorts ctx t_ctx tv 0 te_var := {
  concretize_interp_te_var _ _ _ (TEVAnon _) val := val;
  concretize_interp_te_var _ _ _ (TEVNamed _) val := val;
}.

Definition concretize_interp_te t_ctx ctx tv n ty_expr: interp_te abstract_sorts interp_abstract_sorts t_ctx ctx tv n (abstract_ty_expr ty_expr) = interp_te inner_sorts interp_inner_sorts t_ctx ctx tv n ty_expr.
Proof.
  dependent induction ty_expr; autorewrite with abstract_ty_expr.
  - autorewrite with abstract_ty_expr.
    dependent destruction t; now autorewrite with abstract_ty_expr_var.
  - autorewrite with interp_te; simpl.
    now rewrite IHty_expr1, IHty_expr2.
Defined.

Definition concretize_interp_te' t_ctx ctx tv ty_expr: interp_te abstract_sorts interp_abstract_sorts t_ctx ctx tv 0 (abstract_ty_expr ty_expr) -> interp_te inner_sorts interp_inner_sorts t_ctx ctx tv 0 ty_expr.
Proof.
  intro.
  now rewrite concretize_interp_te in X.
Defined.


(* 
  Synthesize the term by swapping the map in the params HList to get an HList over the
  original arguments, use the equality of the interpretations, use HList map to 
  convert the interpreted abstract arguments back to their original values.
*)
Local Obligation Tactic := intros.
Equations
  interp_abstract_funs 
    t_ctx ctx args ret 
    (fn: abstract_funs t_ctx args ret) tv 
    (hargs: HList.t (interp_te abstract_sorts interp_abstract_sorts t_ctx ctx tv 0) args) 
: interp_te abstract_sorts interp_abstract_sorts t_ctx ctx tv 0 ret := {
  interp_abstract_funs _ _ _ _ (abstract_inner_fun _ _ _ inner_fun) _ args := 
    let swapped := HList.map_swap _ _ args in 
      _;
}.
Next Obligation.
erewrite concretize_interp_te.
eapply interp_inner_funs; eauto.
eapply HList.map.
2: eapply swapped.
intros.
simpl in X.
eapply concretize_interp_te'.
exact X.
Defined.

Variable interp_inner_rels:
  forall t_ctx ctx args (fn: inner_rels t_ctx args) tv
    (hargs: HList.t (interp_te inner_sorts interp_inner_sorts t_ctx ctx tv 0) args),
    Prop
.

Equations
  interp_abstract_rels 
    t_ctx ctx args 
    (fn: abstract_rels t_ctx args) tv 
    (hargs: HList.t (interp_te abstract_sorts interp_abstract_sorts t_ctx ctx tv 0) args) 
: Prop := {
  interp_abstract_rels _ _ _ (abstract_inner_rel _ _ inner_rel) _ args := 
    let swapped := HList.map_swap _ _ args in 
      _;
}.
Next Obligation.
eapply interp_inner_rels; eauto.
eapply HList.map.
2: eapply swapped.
intros.
simpl in X.
eapply concretize_interp_te'.
exact X.
Defined.


Program Definition abstract_model : interp_sig abstract_sorts interp_abstract_sorts abstract_sig := {|
  interp_funs := interp_abstract_funs;
  interp_rels := interp_abstract_rels;
|}.

Definition inner_sig : signature inner_sorts := {| 
  sig_funs := inner_funs;
  sig_rels := inner_rels;
|}.

Fixpoint get_poly_context {ctx} (pfm: poly_fm inner_sorts inner_sig ctx) : ty_ctx :=
  match pfm with 
  | PFm _ => ctx
  | PForall inner => 
    get_poly_context inner
  end.

Fixpoint get_poly_fm {ctx} (pfm: poly_fm inner_sorts inner_sig ctx) : fm inner_sorts inner_sig (get_poly_context pfm) SLNil := 
  match pfm with 
  | PFm f => f
  | PForall inner => get_poly_fm inner
  end.

(* TODO: walk the term and rewrite function and relation symbols; prove the two are bi-satisfactory *)
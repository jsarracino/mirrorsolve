From elpi Require Import elpi.

Elpi Db types.db lp:{{ 
  pred types o:term.
}}.

Elpi Command get_types.
Elpi Accumulate Db types.db.
Elpi Accumulate lp:{{
  main [] :- 
    std.findall (types T_) L, !, coq.say "The current set of types is" L.
}}.
Elpi Typecheck.

Elpi get_types.

Elpi Command add_type.
Elpi Accumulate Db types.db.
Elpi Accumulate lp:{{
  main [str Nme] :- 
    coq.locate Nme GR,
    coq.elpi.accumulate _ "types.db" 
      (clause _ _ (types (global GR))).
}}.
Elpi Typecheck.

Elpi add_type "nat".
Elpi add_type "list".
Elpi get_types.



(* Section AB.

  Variable (A B : Type).

  Inductive simple_typs := 
    | A_ty | B_ty | AB_ty.

  Definition interp_typs ty := 
    (match ty with 
    | A_ty => A 
    | B_ty => B 
    | AB_ty => A * B
    end)%type.

  Inductive simple_funs : list simple_typs -> simple_typs -> Type := 
    | prod_fun : simple_funs [A_ty ; B_ty] AB_ty.

  Equations interp_funs : forall args ret, 
    simple_funs args ret -> 
    HList.t interp_typs args -> 
    interp_typs ret := 
  {
    interp_funs _ _ prod_fun (l ::: r ::: _) := (l, r);
  }.

End AB.


Inductive poly_types := 
  | single_poly_ty : forall (T: Type), poly_types
  | pair_poly_ty : 
    poly_types -> 
    poly_types -> 
    poly_types.

(* Fixpoint interp_p_typs {Typs} (ty : poly_types Typs) : Typs := 
  (match ty with 
  | single_poly_ty T => T
  | pair_poly_ty l r => (interp_p_typs l) * (interp_p_typs r)
  end)%type. *)

Fixpoint interp_p_typs (ty : poly_types) := 
  (match ty with 
  | single_poly_ty T => T
  | pair_poly_ty l r => (interp_p_typs l) * (interp_p_typs r)
  end)%type.

Inductive poly_funs : 
  list poly_types -> poly_types -> Type := 
  | prod_poly_fun : 
    forall (l r : poly_types), 
      poly_funs [l ; r ] (pair_poly_ty l r).


Equations interp_poly_funs : forall args ret, 
  poly_funs args ret -> 
  HList.t interp_p_typs args -> 
  interp_p_typs ret := 
{
  interp_poly_funs _ _ (prod_poly_fun _ _) (l ::: r ::: _) := (l, r);
}.

Arguments interp_poly_funs {_ _}.

Definition foo : HList.t interp_p_typs
  [pair_poly_ty (single_poly_ty nat) (single_poly_ty nat);
  single_poly_ty bool].
refine ( _ ::: _ ::: hnil).
- refine (1, 2).
- refine (true).
Defined.

Eval vm_compute in 
  interp_poly_funs 
    (prod_poly_fun (pair_poly_ty (single_poly_ty nat) (single_poly_ty nat)) (single_poly_ty bool)) 
    foo.


Inductive poly_types (Tys: Type) : Type := 
  | single_poly_ty : forall (T: Tys), poly_types Tys
  | pair_poly_ty : 
    poly_types Tys -> 
    poly_types Tys -> 
    poly_types Tys.

Arguments single_poly_ty {_}.
Arguments pair_poly_ty {_}.

(* Fixpoint interp_p_typs {Typs} (ty : poly_types Typs) : Typs := 
  (match ty with 
  | single_poly_ty T => T
  | pair_poly_ty l r => (interp_p_typs l) * (interp_p_typs r)
  end)%type. *)

Fixpoint interp_p_typs (ty : poly_types Type) := 
  (match ty with 
  | single_poly_ty T => T
  | pair_poly_ty l r => (interp_p_typs l) * (interp_p_typs r)
  end)%type.

Inductive poly_funs (Tys: Type) : 
  list (poly_types Tys) -> (poly_types Tys) -> Type := 
  | prod_poly_fun : forall (l r : poly_types Tys), 
    poly_funs Tys [l ; r ] (pair_poly_ty l r).

Arguments poly_funs {_}.

Equations interp_poly_funs : forall args ret, 
  @poly_funs Type args ret -> 
  HList.t interp_p_typs args -> 
  interp_p_typs ret := 
{
  interp_poly_funs _ _ (prod_poly_fun _ _) (l ::: r ::: _) := (l, r);
}.

Check interp_poly_funs. *)


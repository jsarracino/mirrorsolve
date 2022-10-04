From MetaCoq.Template Require Import All Loader.
Require Import MirrorSolve.Utils.

Import MCMonadNotation.
Open Scope bs.

Require Import Coq.Lists.List.
Import ListNotations.

Definition coerce {A} (x: (option A)) := 
  match x with 
  | Some v => tmReturn v
  | None => tmFail "coerce"
  end.

Definition is_prop_t (t: term) := 
  match t with 
  | tSort u => Universe.is_prop u
  | _ => false
  end.

Print Universe.is_type_sort.

Definition is_type_t (t: term) := 
  match t with 
  | tSort u => Universe.is_type_sort u
  | _ => false
  end.

Definition is_set_t (t: term) := 
  match t with 
  | tSort u => Universe.is_type_sort u
  | _ => false
  end.

Definition is_fo_kind (t: term) := (is_type_t t || is_set_t t)%bool.

Definition check_ind_params (t: mutual_inductive_body) := 
  List.fold_left 
    orb 
    (List.map (fun x => is_fo_kind (x.(decl_type))) t.(ind_params)) 
    true.

Definition fo_context := list (term * bool). (* true values are f-o types and false values are not *)

Require Import MirrorSolve.Utils.
Require Import MirrorSolve.Reflection.Core.

(* Algorithm:
    1) first check that the inductive has type 
      forall (T_i : Type/Set), Type/Set
    2) then check F for first-orderness assuming T_i are first order
*)

Fixpoint strip_prod_prefix (t: term) (n: nat) : option term := 
  match n with 
  | 0 => Some t
  | S n => 
    match t with 
    | tProd _ _ bod => strip_prod_prefix bod n
    | _ => None
    end
  end.

Definition adjust_ind_ty (t: term) (c: context) := strip_prod_prefix t (length c).

Definition is_fo_ind_ty (ind: one_inductive_body) : bool := 
  match adjust_ind_ty ind.(ind_type) ind.(ind_indices) with 
  | Some t => is_fo_kind t
  | None => false
  end.

Fixpoint make_param_prefix (ctx: fo_context) (n: nat) : fo_context := 
  match n with 
  | 0 => (tRel n, true) :: ctx
  | S n' => (tRel n, true) :: make_param_prefix ctx n'
  end.

Fixpoint validate_fo_type (ctx: fo_context) (t: term) : option bool := 
  match t with 
  | tApp f xs => 
    let inner := (let fix rec acc := 
      match acc with 
      | [] => Some true 
      | x :: xs' => 
        match (validate_fo_type ctx x, rec xs') with 
        | (Some b, Some b') => Some (b && b')%bool
        | (_, _) => None
        end
      end in rec xs) in 
    match validate_fo_type ctx f, inner with 
    | Some b, Some b' => Some (b && b')%bool
    | _, _ => None
    end
  | tProd _ ty bod => 
    match validate_fo_type ctx ty with 
    | Some true => 
      let ctx' := map Utils.inc_subst_var ctx in 
        validate_fo_type ((tRel 0, is_fo_kind ty) :: ctx') bod
    | Some false => Some false
    | None => None
    end
  | _ => find _ _ eq_term t ctx
  end.

Definition all_bool xs := List.fold_left andb xs true.

Definition all_map {A} (f: A -> bool) xs := 
  all_bool (List.map f xs).

Fixpoint opt_seq {A} (xs : list (option A)) : option (list A) := 
  match xs with 
  | [] => Some []
  | Some x :: xs' => 
    match opt_seq xs' with 
    | Some xs'' => Some (x :: xs'')
    | _ => None
    end
  | None :: _ => None
  end.

Definition validate_fo_ind (ctx: fo_context) (ind: one_inductive_body) (parent: mutual_inductive_body) := 
  (* assume the original ind type and also the indices are valid FO-types *)
  let param_len := length parent.(ind_params) in 
  let ctx' := make_param_prefix ctx param_len in 
    (* validate_fo_type ctx' ind.(ind_type). *)
  match strip_prod_prefix ind.(ind_type) param_len with 
  | Some t => 
    let parent_ind_ok := is_fo_kind t in 
    let ctors_inner := List.map (fun ctor => 
      match strip_prod_prefix ctor.(cstr_type) param_len with 
      | Some t' => validate_fo_type ctx' t'
      | None => None
      end) ind.(ind_ctors) in 
    match opt_seq ctors_inner with 
    | Some ctors => Some (all_bool ctors && parent_ind_ok)%bool
    | None => None
    end
  | _ => None
  end.

Definition run_add (ctx: fo_context) (t: term) : TemplateMonad (option fo_context) :=
  match t with 
  | tInd ind _ => 
    inds <- tmQuoteInductive ind.(inductive_mind) ;;
    ind' <- coerce (nth_error inds.(ind_bodies) ind.(inductive_ind)) ;;
    let ctx_inner := make_param_prefix ctx (length inds.(ind_params)) in 
    match validate_fo_ind ctx_inner ind' inds with 
    | Some b => tmReturn (Some ((t, b) :: ctx))
    | None => tmReturn None
    end
  | _ => tmFail "run_add"
  end.

(* Print constant_body. *)

(* End-to-end algorithm:

  1) quote recursively;
  2) add each declaration, in order, to a first-order typing context
    2a) special-case nat, bool, Z, N, and pos
    2b) handle inductives using the definition above
    2c) skip definitions
    2d) figure out section variables...not sure how they present
  3) lookup and return the original term's value in the resulting context
*)
From MetaCoq.Template Require Import All Loader.
Require Import MirrorSolve.Utils.

Import MCMonadNotation.
Open Scope bs.

Require Import Coq.Lists.List.
Import ListNotations.

Polymorphic Definition coerce {A} (x: (option A)) := 
  match x with 
  | Some v => tmReturn v
  | None => tmFail "coerce"
  end.

Definition is_prop_t (t: term) := 
  match t with 
  | tSort u => Universe.is_prop u
  | _ => false
  end.

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

Polymorphic Fixpoint is_prop_prod (t: term) := 
  match t with 
  | tProd _ _ b => is_prop_prod b
  | _ => is_prop_t t
  end.

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

Polymorphic Fixpoint validate_fo_type (ctx: fo_context) (t: term) : option bool := 
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

Require MirrorSolve.Reflection.FM.

Polymorphic Fixpoint validate_fo_term (ctx_ty: fo_context) (ctx_term: fo_context) (t: term) : option bool :=
  match t with 
  | tApp _ es => 
    let worker t := 
      match validate_fo_term ctx_ty ctx_term t with 
      | Some b => Some b
      | None => validate_fo_type ctx_ty t
      end in 
    match opt_seq (map worker es) with 
    | Some bs' => Some (all_bool bs')
    | None => None
    end
  | _ => find _ _ eq_term t ctx_term
  end.

Polymorphic Fixpoint validate_fo_prop (ctx_ty: fo_context) (ctx_term: fo_context) (t: term) : option bool := 
  if (eq_term t FM.c_True || eq_term t FM.c_False)%bool then Some true else
  match t with
  | tApp f es => 
    if eq_term f FM.c_eq then 
      match es with 
      | t_ty :: tl :: tr :: _ => validate_fo_type ctx_ty t_ty
      | _ => None
      end
    else if (eq_term f FM.c_or || eq_term f FM.c_and)%bool then 
      match es with 
      | tl :: tr :: _ => 
        match validate_fo_prop ctx_ty ctx_term tl, validate_fo_prop ctx_ty ctx_term tl with 
        | Some l, Some r => Some (l && r)%bool
        | _, _ => None
        end
      | _ => None
      end
    else if eq_term f FM.c_not then 
      match es with 
      | x :: _ => validate_fo_prop ctx_ty ctx_term x
      | _ => None
      end
    else
      let worker t := 
        match validate_fo_term ctx_ty ctx_term t with 
        | Some b => Some b
        | None => validate_fo_type ctx_ty t
        end in 
      match opt_seq (map worker es) with 
      | Some bs' => Some (all_bool bs')
      | None => None
      end
  | tProd ba_name ty bod =>
    match ba_name.(binder_name) with 
    | nAnon => 
      match validate_fo_prop ctx_ty ctx_term ty, validate_fo_prop ctx_ty (map Utils.inc_subst_var ctx_term) bod with 
      | Some el, Some er => Some (el && er)%bool
      | _, _ => None
      end
    | nNamed _ => 
      match validate_fo_type ctx_ty ty with 
      | Some b_ty => 
        let ctx_term' := (tRel 0, b_ty) :: (map Utils.inc_subst_var ctx_term) in 
        validate_fo_prop ctx_ty ctx_term' bod
      | None => None
      end
    end
  | _ => None
  end.

Polymorphic Fixpoint norm_lambda (t: term) : term := 
  match t with 
  | tLambda name ty bod => 
    tProd name ty (norm_lambda bod)
  | _ => t
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

Polymorphic Definition run_once_type (ctx: fo_context) (t: term) : TemplateMonad (option bool) :=
  match t with 
  | tInd ind _ => 
    inds <- tmQuoteInductive ind.(inductive_mind) ;;
    ind' <- coerce (nth_error inds.(ind_bodies) ind.(inductive_ind)) ;;
    if is_prop_prod (ind'.(ind_type)) then tmReturn None else
    let ctx_inner := make_param_prefix ctx (length inds.(ind_params)) in 
    tmReturn (validate_fo_ind ctx_inner ind' inds)
  | _ => 
    tmReturn (validate_fo_type ctx t)
  end.

Definition builtin_names := [
      (MPfile ["BinNums"; "Numbers"; "Coq"], "Z")
    ; (MPfile ["Datatypes"; "Init"; "Coq"], "bool")
  ].

Polymorphic Definition handle_one_decl (ctx: fo_context) (g: kername * global_decl) : TemplateMonad (option fo_context) := 
  match g.2 with 
  | ConstantDecl _ => 
    (* tmPrint "skipping const decl for" ;; 
    x <- tmEval all g.1 ;; 
    tmPrint x ;; *)
    tmReturn (Some ctx)
  | InductiveDecl mi_bod => 
    tmReturn (
    if inb _ eq_kername g.1 builtin_names then Some ((tInd (mkInd g.1 0) [], true) :: ctx)
    else
    match mi_bod.(ind_bodies) with 
    | [ind'] => 
      if is_prop_prod ind'.(ind_type) then Some ctx else
      let ctx_inner := make_param_prefix ctx (length mi_bod.(ind_params)) in 
        match validate_fo_ind ctx_inner ind' mi_bod with 
        | Some b => Some ((tInd (mkInd g.1 0) [], b) :: ctx)
        | None => None
        end
    | _ => Some ctx
    end)
  end.

Polymorphic Definition handle_decls_worker (acc: option fo_context ) (d: kername * global_decl) : TemplateMonad (option fo_context) := 
  match acc with 
  | Some acc' => handle_one_decl acc' d 
  | _ => tmReturn None
  end.

Polymorphic Definition handle_all_decls (ctx: fo_context) (gs: list (kername * global_decl)) : TemplateMonad (option fo_context) := 
  foldlM handle_decls_worker (Some ctx) gs.

Polymorphic Definition get_type {A} (_: A) : TemplateMonad term := 
  tmQuote A.

Polymorphic Definition get_type_term (x: term) : TemplateMonad term := 
  x <- tmUnquote x ;;
  x <- tmEval all x.(my_projT1) ;;
  tmQuote x.

Polymorphic Fixpoint extract_vars (t: term) : list term := 
  match t with 
  | tVar _ => [t]
  | tProd _ ty bod => extract_vars ty ++ extract_vars bod
  | tLambda _ ty bod => extract_vars ty ++ extract_vars bod
  | tLetIn _ ty v bod => extract_vars ty ++ extract_vars v ++ extract_vars bod
  | tApp f args => 
    extract_vars f ++ List.concat (List.map extract_vars args)
  | tProj _ x => extract_vars x
  | _ => []
  end.

Polymorphic Definition preprocess_vars (t: term) : TemplateMonad fo_context := 
  mapM (fun x => ty <- get_type_term x ;; tmReturn (x, is_fo_kind ty)) (uniq _ eq_term (extract_vars t)).


Polymorphic Definition is_fo_type (p: program) : TemplateMonad (option bool) :=
  (* tmPrint "decls:" ;; 
  x <- tmEval all p.1.(declarations) ;; 
  tmPrint x ;; *)
  ctx <- preprocess_vars p.2 ;;
  (* tmPrint "init ctx:" ;; 
  x <- tmEval all ctx ;; 
  tmPrint x ;; *)
  r <- handle_all_decls ctx (List.rev (p.1.(declarations)));;
  match r with 
  | Some ctx' => 
    (* tmPrint "ctx:" ;; 
    tmPrint ctx' ;;
    tmPrint "term:" ;; 
    x <- tmEval all p.2 ;;
    tmPrint x ;; *)
    run_once_type ctx' p.2
  | None => tmReturn None
  end.


Polymorphic Definition quoteConstRec {A} (a: A) : TemplateMonad program := 
  x <- tmQuote a ;; 
  match x with 
  | tConst name _ => 
    y <- tmQuoteConstant name false ;; 
    match y.(cst_body) with 
    | Some t => 
      inter <- tmUnquote t ;; 
      inter <- tmEval all (my_projT2 inter) ;;
      tmQuoteRec inter
    | _ => 
      tmPrint x ;;
      tmFail "opaque/undefined constant in quoteConstRec"
    end
  | _ => 
    tmPrint x ;; 
    tmFail "quoteConstRec passed a non-constant input"
  end.

Polymorphic Definition is_fo_const {A} (a: A) : TemplateMonad (option bool) := 
  p <- quoteConstRec a ;;
  let t := norm_lambda p.2 in 
  ctx <- preprocess_vars t ;;
  (* tmPrint "init ctx:" ;; 
  x <- tmEval all ctx ;; 
  tmPrint x ;; *)
  r <- handle_all_decls ctx (List.rev (p.1.(declarations))) ;;
  match r with 
  | Some ctx' => tmReturn (validate_fo_prop ctx' [] t)
  | _ => tmReturn None
  end.

(* Section Foo.
Variable (X: Type).
Definition foo := forall (x: X), (fun y => y = x) = (fun z => z = x).

MetaCoq Run (
  MetaCoq.Template.TemplateMonad.Core.tmBind (is_fo_const foo)  (fun x => 
  MetaCoq.Template.TemplateMonad.Core.tmBind (MetaCoq.Template.TemplateMonad.Core.tmEval MetaCoq.Template.TemplateMonad.Common.all x) (fun x => 
  MetaCoq.Template.TemplateMonad.Core.tmPrint x
))). *)

(* Section Foo.
Variable (A: Type).
Variable (B: Type).
Variable f: A -> B.

MetaCoq Run (
  x <- tmQuote (A, B, f) ;;
  x <- preprocess_vars x ;;
  x <- tmEval all x ;; 
  tmPrint x
). *)


From MetaCoq.Template Require Import All Loader.
Import MCMonadNotation.

Require Import Coq.Strings.String.

Require Import Coq.Lists.List.
Open Scope bs.

Definition mk_ctor_body (x: ident) : constructor_body := {| 
  cstr_name := "sort_" ++ x;
  cstr_args := [];
  cstr_indices := [];
  cstr_type := tRel 0;
  cstr_arity := 0;
|}.

MetaCoq Quote Definition set_term := (Set).
MetaCoq Quote Definition typ_term := (Type).


Definition sorts_one_body (names: list ident) : one_inductive_body := {|
  ind_name := "sorts";
  ind_indices := [];
  ind_sort := Universe.type1;
  ind_type := set_term;
  ind_kelim := IntoAny;
  ind_ctors := List.map mk_ctor_body names;
  ind_projs := [];
  ind_relevance := Relevant
|}.

Definition sorts_body (names: list ident) : mutual_inductive_body := {| 
  ind_finite := Finite;
  ind_npars := 0;
  ind_params := [];
  ind_bodies := [
    sorts_one_body names
  ];
  ind_universes := Monomorphic_ctx;
  ind_variance := None;
|}.

Definition add_sorts (names: list ident) := tmMkInductive' (sorts_body names).

Universe sorts_level.

Definition make_interp_branch (r: term) : branch term :=  {|
  bcontext := [];
  bbody := r
|}.

Definition packed_ty := {T & T}.

Fixpoint tm_make_interp_branches (xs: list packed_ty) : TemplateMonad (list (branch term)) := 
  match xs with 
  | nil => tmReturn nil
  | (existT _ x) :: xs' => 
    t <- tmQuote x ;;
    r <- tm_make_interp_branches xs' ;;
    tmReturn (make_interp_branch t :: r)
  end.

Definition quote_dest_ind (t: Type) := 
  sorts_term <- tmQuote t ;;
  match sorts_term with 
  | tInd ind _ => tmReturn (sorts_term, ind)
  | _ => 
    tmMsg "sort input was not actually a inductive!" ;; 
    tmPrint sorts_term ;;
    tmFail "bad sort input"
  end.


Definition add_interp_sorts (tys: list packed_ty) (sorts: Type) := 
  '(sort_term, ind) <- quote_dest_ind sorts ;;
  brs <- tm_make_interp_branches tys ;;
  tmMkDefinition "interp_sorts" (tLambda 
    (mkBindAnn (nNamed "srt") Relevant)
    sort_term
    (tCase {| 
      ci_ind := ind;
      ci_npar := 0;
      ci_relevance := Relevant;
      |} {|
        puinst := [];
        pparams := [];
        pcontext := [(mkBindAnn (nNamed "srt") Relevant)];
        preturn := tSort (Universe.of_levels (inr (Level.Level "sorts_level")))
      |} 
      (tRel 0)
      brs
    )
  ).

MetaCoq Quote Definition term_nat := nat.
MetaCoq Quote Definition term_0 := 0.

(* Inductive fin : nat -> Set := f0 : fin 0. *)

MetaCoq Quote Definition narr := (nat -> Set).

Definition map_with_index {A B} (f: nat -> A -> B) (xs: list A) : list B := 
  (fix rec xs acc :=
    match xs with 
    | nil => nil
    | x :: xs' => f acc x :: rec xs' (S acc)
    end
  ) xs 0.

Require Coq.Strings.BinaryString.

Print string.

Definition n_to_str (n: nat) : string := 
  BinaryString.of_nat n.

Definition mk_fun_ctor (i: nat) (indices: list term) : constructor_body := {| 
  cstr_name := "f" ++ (String.of_string (n_to_str i));
  cstr_args := [];
  cstr_indices := [];
  cstr_type := tApp (tRel 0) indices;
  cstr_arity := 0;
|}.

Definition funs_one_body (fun_args_term: term) (fun_ret_term: term) (indices: list (list term)) (funs_type: term) : one_inductive_body := {|
  ind_name := "fol_funs";
  ind_indices := [ {| 
      decl_name := (mkBindAnn nAnon Relevant);
      decl_body := None;
      decl_type := fun_args_term;
    |} ; {| 
      decl_name := (mkBindAnn nAnon Relevant);
      decl_body := None;
      decl_type := fun_ret_term;
    |}
  ];
  ind_sort := Universe.type1;
  ind_type := funs_type;
  ind_kelim := IntoAny;
  ind_ctors := map_with_index mk_fun_ctor indices;
  ind_projs := [];
  ind_relevance := Relevant
|}.

Definition funs_body (funs_arg_term : term) (funs_ret_term: term) (indices: list (list term)) (funs_type : term) : mutual_inductive_body := {| 
  ind_finite := Finite;
  ind_npars := 0;
  ind_params := [];
  ind_bodies := [
    funs_one_body funs_arg_term funs_ret_term indices funs_type
  ];
  ind_universes := Monomorphic_ctx;
  ind_variance := None;
|}.

Locate kername.

Definition get_typ (x: global_decl) := 
  match x with 
  | ConstantDecl body => body.(cst_type)
  | InductiveDecl mind => hole
  end.

Fixpoint normalize_sort_term (t: term) : list term := 
  match t with 
  | tProd _ ty bod => normalize_sort_term ty ++ normalize_sort_term bod
  | tInd _ _ => [t] 
  | tVar _ => [t]
  | tApp l rs => 
    normalize_sort_term l ++ concat (map normalize_sort_term rs)
  | _ => []
  end.

Require Import MirrorSolve.Utils.
Import KernameComp.
Definition kername_eqb l r :=
  match compare l r with 
  | Eq => true
  | _ => false
  end.

Definition eq_kname : kername := (MPfile ["Logic"; "Init"; "Coq"], "eq").
Definition pos_kname : kername := (MPfile ["BinNums"; "Numbers"; "Coq"], "positive").

Definition should_filter (k: kername) := inb _ kername_eqb k [eq_kname; pos_kname].

Fixpoint get_sorts' ( decls: global_declarations ) : list term := 
  match decls with 
  | nil => nil
  | (kn, decl) :: decls' => 
    let r := get_sorts' decls' in 
      if should_filter kn then r else 
      match decl with 
      | ConstantDecl cd => normalize_sort_term cd.(cst_type) ++ r
      | _ => r
      end
  end.

Require MirrorSolve.Reflection.Core.

Definition get_sorts decls := uniq _ Core.eq_term (get_sorts' decls).

Fixpoint quote_indices (sorts: Type) (indices : list (list sorts * sorts)) : TemplateMonad (list (list term)) :=
  match indices with 
  | nil => tmReturn nil
  | (args, ret) :: indices' => 
    args_term <- tmQuote args ;;
    ret_term <- tmQuote ret ;;
    r <- quote_indices _ indices' ;;
    tmReturn ([args_term; ret_term] :: r)
  end.

Definition add_funs_type (sorts: Type) (indices : list (list sorts * sorts)) : TemplateMonad unit := 
  arg_term <- tmQuote (list sorts) ;;
  ret_term <- tmQuote sorts ;;
  funs_ty_term <- tmQuote (list sorts -> sorts -> Type) ;;
  indices' <- quote_indices sorts indices ;;
  tmMkInductive' (funs_body arg_term ret_term indices' funs_ty_term).


Definition make_names (prefix: ident) (xs: list term) : list ident := 
  map_with_index (fun i _ => prefix ++ "_" ++ (String.of_string (n_to_str i))) xs.

Definition uniq_term := uniq _ Core.eq_term.


(* TODO: 
  1) add a new sort interpretation, unquoting sort_ty_terms to get the types
  2) add function symbols, using the new sort and the indices as constructor arguments
  
*)
Definition add_funs_indices (indices: list (list term)) := 
  let sort_ty_terms := uniq_term (concat indices) in 
  let sort_names := make_names "srt" sort_ty_terms in 
  add_sorts sort_names.


(* MetaCoq Run (add_funs_indices [[tRel 0; tRel 1]]). *)


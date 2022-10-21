From MetaCoq.Template Require Import All Loader.
Import MCMonadNotation.
Require Import MirrorSolve.SMT.

Require Import Coq.Strings.String.

Require Import Coq.Lists.List.
Require Import MirrorSolve.HLists.
Import HListNotations.
Open Scope bs.


Universe sorts_level.

Require MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Utils.
  
(* Quote a term twice, i.e. get a term that corresponds to the quoted term of x.
   This is useful for writing metafunctions (e.g. generating the branches of a term match statement)
*)
Polymorphic Definition tmQuote2 {X} (x: X) := 
  tmQuote x >>= tmQuote.

Polymorphic Definition make_ind_ctor (ind: inductive) (u: Instance.t) (idx: nat) (x: constructor_body) : term := 
  tConstruct ind idx u.

(* given a list of terms, return a term that when evaluated, will produce a list of unquoted terms
 *)
Polymorphic Fixpoint make_list {A} (ts: list term) : TemplateMonad term := 
  match ts with 
  | nil => 
    nil_t <- tmQuote (@nil A) ;;
    tmReturn nil_t
  | t :: ts' => 
    v <- tmUnquoteTyped A t ;;
    vs_term <- @make_list A ts' ;;
    vs <- tmUnquoteTyped (list A) vs_term ;;
    tmQuote (v :: vs)
  end.

Polymorphic Definition lookup_ind (x: inductive) : TemplateMonad one_inductive_body := 
  parent_inds <- tmQuoteInductive x.(inductive_mind) ;;
  match nth_error parent_inds.(ind_bodies) x.(inductive_ind) with 
  | Some x => tmReturn x 
  | None => tmFail "error looking up inductive?"
  end.

Polymorphic Definition lookup_ty (t: term) : TemplateMonad term := 
  foo <- tmUnquote t ;;
  ty <- tmEval all (my_projT1 foo) ;;
  tmQuote ty.


Fixpoint str_join (xs: list ident) (sep: ident) : ident := 
  match xs with 
  | [] => ""
  | [x] => x 
  | x :: xs' => 
    x ++ sep ++ str_join xs' sep
  end.

MetaCoq Quote Definition t_z := (BinInt.Z).
MetaCoq Quote Definition t_bool := (bool).
MetaCoq Quote Definition t_prop := (Prop).
Definition is_z_srt t := Core.eq_term t t_z.
Definition is_b_srt t := Core.eq_term t t_bool.

Polymorphic Fixpoint get_ty_name (t: term) : TemplateMonad ident := 
  if is_z_srt t then 
    tmReturn "Int"
  else if is_b_srt t then 
    tmReturn "Bool"
  else
    match t with 
    | tInd ind _ => tmReturn (ind.(inductive_mind).2)
    | tApp f es => 
      pref <- get_ty_name f ;;
      rhses <- mapM get_ty_name es ;;
      tmReturn (pref ++ "_" ++ str_join rhses "_")
    | tVar s => tmReturn s
    | tSort (Universe.lProp) => tmReturn "Prop"
    | _ => 
      tmMsg "can't get name from:" ;;
      tmPrint t ;;
      tmFail "get_ty_name"
    end.

Polymorphic Fixpoint subst_var (v: nat) (r: term) (t: term) := 
  match t with 
  | tRel n => 
    if Nat.eqb v n then r else t
  | tApp f es => 
    tApp (subst_var v r f) (map (subst_var v r) es)
  | tProd x ty bod => 
    tProd x (subst_var v r ty) (subst_var (S v) r bod)
  | _ => t
  end.

Polymorphic Fixpoint apply_args (t: term) (args: list term) : option term := 
  match t, args with 
  | tProd x _ bod, arg :: args' => 
    apply_args (subst_var 0 arg bod) args'
  | _, _ :: _ => None
  | _, [] => Some t
  end.

(* given a constant or a constructor for a inductive, return the name of the constant/constructor. *)
Polymorphic Fixpoint get_global_name (t: term) : TemplateMonad ident := 
  match t with 
  | tConst x _ => tmReturn x.2
  | tConstruct ind i _ => 
    parent_ind <- lookup_ind ind ;; 
    match nth_error parent_ind.(ind_ctors) i with 
    | Some x => tmReturn x.(cstr_name)
    | None => tmFail "error looking up constructor in get_global_name"
    end
  | tVar x => tmReturn x
  | tApp f es => 
    pref <- get_global_name f ;;
    rhses <- mapM get_global_name es ;;
    tmReturn (pref ++ "_" ++ str_join rhses "_")
  | tInd ind _ => tmReturn ind.(inductive_mind).2
  | _ => 
    tmPrint t ;;
    tmFail "get_global_name called with not a const or constructor"
  end.


Require Import MirrorSolve.FirstOrder.

Section Config.

  Set Universe Polymorphism.

  (* Helper functions for building sort inductives *)

  Definition mk_ctor_body (x: ident) : constructor_body := {| 
    cstr_name := "sort_" ++ x;
    cstr_args := [];
    cstr_indices := [];
    cstr_type := tRel 0; (* The parent type (i.e. sorts) *)
    cstr_arity := 0;
  |}.

  MetaCoq Quote Definition set_term := (Set).
  MetaCoq Quote Definition typ_term := (Type@{sorts_level}).

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

  Definition mk_sorts_ctor (ind: inductive) (u: Instance.t) (i: nat) (name: ident) : term := 
    tConstruct ind i u.

  (* Given a list of names for sorts, make an inductive type with constructors for each name.
    e.g. add_sorts ["bool"; "int"] adds an inductive sorts := sort_bool | sort_int, 
    and returns terms for the new constructors e.g. [sort_bool; sort_int]
  *)
  Definition add_sorts (names: list ident) : TemplateMonad (list term) := 
    tmMkInductive' (sorts_body names) ;;
    tmPrint "added inductive definition for sorts" ;;
    srt <- tmLocate1 "sorts" ;; 
    match srt with 
    | IndRef i => tmReturn (map_with_index (mk_sorts_ctor i []) names)
    | _ => tmFail "sorts is not an inductive!"
    end.

  (* helper functions for building the semantics of sorts 
  *)

  

  Definition make_interp_branch (r: term) : branch term :=  {|
    bcontext := [];
    bbody := if Core.eq_term r t_prop then t_bool else r
  |}.

  (* packed types for opaque hlists, so that end-users can combine different functions in the same list *)
  Definition packed := {T & T}.
  Notation pack x := (existT _ _ x).

  Definition tmQuotePacked (x: packed) := 
    match x with 
    | pack x' => tmQuote x'
    end.

  Definition tm_make_interp_branches (xs: list term) : TemplateMonad (list (branch term)) := 
    tmReturn (map make_interp_branch xs).

  Definition do_one_branch (x: packed) : TemplateMonad (branch term) :=
    tmQuotePacked x >>= (liftM make_interp_branch).

  Definition tm_make_interp_branches_p (xs: list packed) : TemplateMonad (list (branch term)) := 
    mapM do_one_branch xs.

  (* Quote and destruct a type as an inductive, 
     and return the quoted term as well as the inductive *)
  Definition quote_dest_ind (t: Type) := 
    sorts_term <- tmQuote t ;;
    match sorts_term with 
    | tInd ind _ => tmReturn (sorts_term, ind)
    | _ => 
      tmMsg "sort input was not actually a inductive!" ;; 
      tmPrint sorts_term ;;
      tmFail "bad sort input"
    end.

  (* Given a list of quoted RHS types, as well as a type for inductive sorts, 
    add an interpretation function "interp_sorts" which evaluates each constructor of sorts to the corresponding RHS type
    e.g. if sorts := sort_bool | sort_int, then
       add_interp_sorts [quote bool; quote Z] sorts 

       adds a definition:
       Definition interp_sorts (x: sorts) := 
        match x with 
        | sort_bool => bool
        | sort_int => Z
        end.
    *)

  Definition add_interp_sorts (tys: list term) (sorts: Type) := 
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

  (* similar to above but take packed types as input (instead of quoted types, e.g. pack Z) *)

  Definition add_interp_sorts_p (tys: list packed) (sorts: Type) := 
    '(sort_term, ind) <- quote_dest_ind sorts ;;
    brs <- tm_make_interp_branches_p tys ;;
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

  Require Coq.Strings.BinaryString.

  (* helper functions for syntax and semantics of function symbols *)
  Definition n_to_str (n: nat) : string := 
    BinaryString.of_nat n.

  Definition mk_fun_ctor (name: ident) (indices: list term) : constructor_body := {| 
    cstr_name := name ++ "_f";
    cstr_args := [];
    cstr_indices := [];
    cstr_type := tApp (tRel 0) indices;
    cstr_arity := 0;
  |}.


  Definition z_const_ctor (z_const_indices : term) (t_nil : term) : constructor_body := {| 
    cstr_name := "z_const_f";
    cstr_args := [{|
      decl_name :=
        {|
          binder_name := nNamed "z"; binder_relevance := Relevant
        |};
      decl_body := None;
      decl_type :=
        tInd
          {|
            inductive_mind :=
              (MPfile ["BinNums"; "Numbers"; "Coq"], "Z");
            inductive_ind := 0
          |} []
    |}];
    cstr_indices := [tInd
    {|
      inductive_mind :=
        (MPfile ["BinNums"; "Numbers"; "Coq"], "Z");
      inductive_ind := 0
    |} []];
    cstr_type := 
      tProd
        {| binder_name := nNamed "z"; binder_relevance := Relevant |}
        (tInd
          {|
            inductive_mind :=
              (MPfile ["BinNums"; "Numbers"; "Coq"], "Z");
            inductive_ind := 0
          |} [])
        (tApp (tRel 1) [ t_nil ; z_const_indices]);
    cstr_arity := 1;
  |}.

  Definition b_const_ctor (b_const_indices : term) (t_nil : term) : constructor_body := {| 
    cstr_name := "b_const_f";
    cstr_args := [{|
      decl_name :=
        {|
          binder_name := nNamed "b"; binder_relevance := Relevant
        |};
      decl_body := None;
      decl_type :=
        tInd
          {|
            inductive_mind :=
              (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
            inductive_ind := 0
          |} []
    |}];
    cstr_indices := [tInd
    {|
      inductive_mind :=
        (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
      inductive_ind := 0
    |} []];
    cstr_type := 
      tProd
        {| binder_name := nNamed "b"; binder_relevance := Relevant |}
        (tInd
          {|
            inductive_mind :=
              (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
            inductive_ind := 0
          |} [])
        (tApp (tRel 1) [ t_nil ; b_const_indices]);
    cstr_arity := 1;
  |}.


  Definition mk_rel_ctor (name: ident) (indices: list term) : constructor_body := {| 
    cstr_name := name ++ "_r";
    cstr_args := [];
    cstr_indices := [];
    cstr_type := tApp (tRel 0) indices;
    cstr_arity := 0;
  |}.

  Definition const_term_builder t_nil (x: term * smt_fun_base)  := 
    match x.2 with 
    | IntLit => Some (z_const_ctor x.1 t_nil)
    | BoolLit => Some (b_const_ctor x.1 t_nil)
    | _ => None (* should not happen *)
    end.
  

  Definition funs_one_body 
    (t_nil : term) (* quoted nil, needs to be passed due to universe stuff *)
    (fun_args_term: term) (* quoted type of args *)
    (fun_ret_term: term) (* quoted type of ret *)
    (names: list ident)  (* names for each of the function symbols *)
    (indices: list (list term)) (* args + return type indices for individual symbols *)
    (funs_type: term) (* overall type of function symbols *)
    (incl_consts : list (term * smt_fun_base))
    : one_inductive_body * list (nat * smt_fun_base) (* resulting funs inductive, and indices + const type for consts *)
    := 
    let consts := map_option (const_term_builder t_nil) incl_consts in ({|
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
    ind_ctors := 
      List.app 
        (map (fun '(name, idxs) => mk_fun_ctor name idxs) (List.combine names indices))
        consts
        ;
    ind_projs := [];
    ind_relevance := Relevant
  |} , map_with_index (fun i x => (i + length indices, x.2)) incl_consts). 

  (* same arguments as above *)
  Definition funs_body 
    (t_nil: term) 
    (funs_arg_term : term) 
    (funs_ret_term: term) 
    (names: list ident) 
    (indices: list (list term)) 
    (funs_type : term)
    (incl_consts : list (term * smt_fun_base)) : 
    mutual_inductive_body * (inductive -> list (term * smt_fun_base)) (* convert const constructors into terms *)
  := 
    let (bodies, consts) := funs_one_body t_nil funs_arg_term funs_ret_term names indices funs_type incl_consts in ({| 
    ind_finite := Finite;
    ind_npars := 0;
    ind_params := [];
    ind_bodies := [ bodies ];
    ind_universes := Monomorphic_ctx;
    ind_variance := None;
  |}, fun funs_ind => map (fun '(i, sfb) => (tConstruct funs_ind i Instance.empty, sfb)) consts).

  (* analogous arguments as for *)
  Definition rel_one_body (rel_args_term: term)
  (names: list ident) (indices: list (list term)) (rel_type: term) : one_inductive_body := {|
    ind_name := "fol_rels";
    ind_indices := [ {| 
        decl_name := (mkBindAnn nAnon Relevant);
        decl_body := None;
        decl_type := rel_args_term;
      |} 
    ];
    ind_sort := Universe.type1;
    ind_type := rel_type;
    ind_kelim := IntoAny;
    ind_ctors := map (fun '(name, idxs) => mk_rel_ctor name idxs) (List.combine names indices);
    ind_projs := [];
    ind_relevance := Relevant
  |}.

  Definition rel_body (rel_arg_term : term) (names: list ident) (indices: list (list term)) (rel_type : term) : mutual_inductive_body := {| 
    ind_finite := Finite;
    ind_npars := 0;
    ind_params := [];
    ind_bodies := [
      rel_one_body rel_arg_term names indices rel_type
    ];
    ind_universes := Monomorphic_ctx;
    ind_variance := None;
  |}.

  (* get the type of a global constant (possibly crashes for inductives) *)
  Definition get_typ (x: global_decl) := 
    match x with 
    | ConstantDecl body => body.(cst_type)
    | InductiveDecl mind => hole
    end.

  (* flatten a quoted product type into a list of individual terms, e.g.
    normalize_sort_term (quote (bool -> Z -> Z)) => [quote bool; quote Z; quote Z]
  *)
  Fixpoint normalize_sort_term (t: term) : list term := 
    match t with 
    | tProd _ ty bod => normalize_sort_term ty ++ normalize_sort_term bod
    | tInd _ _ => [t] 
    | tVar _ => [t]
    | tApp _ _ => [t]
      (* normalize_sort_term l ++ concat (map normalize_sort_term rs) *)
    (* | tRel _ => [t] *)
    | tSort _ => 
      if Core.eq_term t t_prop then [t] else []
    | _ => []
    end.

  Require Import MirrorSolve.Utils.
  Import KernameComp.
  (* compare two kernal names for quality *)
  Definition kername_eqb l r :=
    match compare l r with 
    | Eq => true
    | _ => false
    end.

  Definition eq_kname : kername := (MPfile ["Logic"; "Init"; "Coq"], "eq").
  Definition pos_kname : kername := (MPfile ["BinNums"; "Numbers"; "Coq"], "positive").

  Definition should_filter (k: kername) := inb _ kername_eqb k [eq_kname; pos_kname].

  (* Get the sorts in a list of declarations. 
     Discard eq and positive because they are not used.
  *)
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

  (* Given a list of decls, return the unique sorts in the decls *)
  Definition get_sorts decls := uniq _ Core.eq_term (get_sorts' decls).

  (* unquote a list of terms to a particular type (sorts) *)
  Fixpoint unquote_indices_helper (sorts: Type) (terms: list term) : TemplateMonad (list sorts) := 
    match terms with 
    | [] => tmReturn []
    | t :: ts => 
      x <- tmUnquoteTyped sorts t ;;
      x' <- unquote_indices_helper sorts ts ;;
      tmReturn (x :: x')
    end.

  (* optionally split a list into a last element and a prefix *)
  Fixpoint get_last {A} (xs: list A) : option (list A * A) := 
    match xs with 
    | nil => None
    | x :: xs => 
      match xs with 
      | nil => Some (nil, x)
      | _ => 
        match get_last xs with 
        | Some (xs', x') => Some (x :: xs', x')
        | None => None
        end
      end
    end.

  (* given a list of quoted type indices,
    unquote the indices and split out the return type index (i.e. the last index)
   *)
  Fixpoint unquote_fun_indices (sorts: Type) (indices: list (list term)) : TemplateMonad (list (list sorts * sorts)) := 
    match indices with 
    | [] => tmReturn []
    | t :: ts => 
      x <- unquote_indices_helper sorts t ;;
      match get_last x with 
      | Some v => 
        r <- unquote_fun_indices sorts ts ;;
        tmReturn (v :: r)
      | None => tmFail "empty indices??"
      end
    end.

  (* Similar for functions, except relations don't have a return type (so we don't need to split out a return type index) *)

  Definition unquote_rel_indices (sorts: Type) (indices: list (list term)) : TemplateMonad (list (list sorts)) := 
    mapM (unquote_indices_helper sorts) indices.

  (* Quote a set of function indices + return types *)
  Fixpoint quote_fun_indices (sorts: Type) (indices : list (list sorts * sorts)) : TemplateMonad (list (list term)) :=
    match indices with 
    | nil => tmReturn nil
    | (args, ret) :: indices' => 
      args_term <- tmQuote args ;;
      ret_term <- tmQuote ret ;;
      r <- quote_fun_indices _ indices' ;;
      tmReturn ([args_term; ret_term] :: r)
    end.

  (* Quote a set of relation indices *)
  Fixpoint quote_rel_indices (sorts: Type) (indices : list (list sorts)) : TemplateMonad (list (list term)) :=
    match indices with 
    | nil => tmReturn nil
    | args :: indices' => 
      args_term <- tmQuote args ;;
      r <- quote_rel_indices _ indices' ;;
      tmReturn ([args_term] :: r)
    end.

  (* Go through a key-value list of sorts and check if Z (or bool) is around. 
     If it is, return the corresponding sort constructor for Z (e.g. sort_Z)
   *)

  

  Fixpoint gather_z_const (srts: list (term * term)) : option term := 
    match srts with 
    | [] => None
    | (typ, idx) :: xs => 
      if is_z_srt typ then Some idx else gather_z_const xs 
    end.
  
  Fixpoint gather_b_const (srts: list (term * term)) : option term := 
    match srts with 
    | [] => None
    | (typ, idx) :: xs => 
      if is_b_srt typ then Some idx else gather_b_const xs 
    end.

  Definition gather_consts (srts: list (term * term)) := 
   (o2l (option_map (fun x => (x, IntLit)) (gather_z_const srts)) ++ 
    o2l (option_map (fun x => (x, BoolLit)) (gather_b_const srts)))%list.

  (* Given a list of function names and corresponding argument + return type indices, 
    make a function symbol inductive declaration.
    Does *not* handle Z constants.
  *)
  Definition add_funs_type (sorts: Type) (names: list ident) (indices : list (list sorts * sorts)) : TemplateMonad unit := 
    arg_term <- tmQuote (list sorts) ;;
    ret_term <- tmQuote sorts ;;
    funs_ty_term <- tmQuote (list sorts -> sorts -> Type) ;;
    nil_term <- tmQuote (@nil sorts) ;;
    indices' <- quote_fun_indices sorts indices ;;
    let '(r, _) := funs_body nil_term arg_term ret_term names indices' funs_ty_term [] in 
    tmMkInductive' r.

  (* Get a name for a simple type (e.g. a section variable or a plain inductive).
  *)

  Definition make_names (xs: list term) : TemplateMonad (list ident) := 
    mapM get_ty_name xs.

  Definition uniq_term := uniq _ Core.eq_term.

  Definition sorts_constant_body (x: constant_body) : list term := 
    normalize_sort_term x.(cst_type).

  Fixpoint skip_ctor_env (env: list (term * term)) (t: term) : option term := 
    match env with 
    | nil => Some t
    | _ :: env' => 
      match t with 
      | tProd _ _ t' => 
        skip_ctor_env env' t'
      | _ => None
      end
    end.

  Definition get_ctor_type (env: list (term * term)) (x: constructor_body) : option (list term) :=
    match env with 
    | [] => None
    | _ :: env' => 
      match skip_ctor_env env' x.(cstr_type) with 
      | Some t' => 
        Some (normalize_sort_term (subst_terms env t'))
      | None => None
      end
    end.
  
  Definition get_ctor_name (x: constructor_body) : ident := x.(cstr_name).

  Definition make_rel_ind_type (t: term) : option (list term) := 
    let tys := normalize_sort_term t in 
    match get_last tys with 
    | Some (_, x) => 
      if Core.eq_term x t_prop then Some tys else None
    | _ => None
    end.

  Definition is_prop_ind (i: inductive) : TemplateMonad bool := 
    ind <- lookup_ind i ;;
    let tys := normalize_sort_term ind.(ind_type) in 
    match get_last tys with 
    | Some (_, x) => tmReturn (Core.eq_term x t_prop)
    | _ => tmReturn false
    end.

  Definition sorts_mind_body (t: term) (args: list term) : TemplateMonad (list (ident * list term)) := 
    match t with 
    | tInd ind  _ => 
      x <- tmQuoteInductive ind.(inductive_mind) ;;
      match x.(ind_bodies) with 
      | [i] => 
        match make_rel_ind_type i.(ind_type) with 
        | Some tys => 
          tmReturn [(i.(ind_name), tys)]
        | None => 
          let env := (tRel (List.length args), t) :: map_with_index (fun i t => (tRel i, t)) (List.rev args) in
          let opt_ctors := map (fun c => 
            match get_ctor_type env c with 
            | Some x => 
              Some (get_ctor_name c, x)
            | None => None
            end) i.(ind_ctors) in
          r <- validate_opts opt_ctors  "couldn't convert constructor parameters" ;; 
          suffixes <- mapM get_ty_name args ;;
          match suffixes with 
          | [] => tmReturn r
          | _ => 
            tmReturn (map (fun '(cn, x) => (cn ++ "_" ++ str_join suffixes "_", x)) r)
          end
        end
      | _ => tmFail "mutually inductive inds are not currently supported"
      end
    | _ => tmFail "sorts_mind_body called with non-ind input"
    end.

  (* Given a packed function or inductive type, 
    return a list of function names and indices for function symbols *)
  Definition gather_sorts (t: packed) : TemplateMonad (list (ident * list term)) := 
    t' <- tmQuotePacked t ;;
    match t' with 
    | tApp (tInd ind u) args => 
      sorts_mind_body (tInd ind u) args
    | tInd _ _ => sorts_mind_body t' []
    | tVar name => 
      ty <- lookup_ty t' ;;
      tmReturn [(name, normalize_sort_term ty)]
    | tApp (tConst name _) args => 
      f <- tmQuoteConstant name true ;;
      match apply_args f.(cst_type) args with 
      | Some r => 
        suffixes <- mapM get_ty_name args ;;
        tmReturn [
          ( name.2 ++ "_" ++ str_join suffixes "_", normalize_sort_term r)
        ]
      | None => 
        v <- tmEval all f.(cst_type) ;;
        tmPrint "type:" ;;
        tmPrint v ;;
        tmPrint "args:" ;;
        tmPrint args ;;
        tmFail "couldn't apply args to parametric function in gather_sorts"
      end 
    | tConst name _ => 
      f <- tmQuoteConstant name true ;;
      tmReturn [(name.2, (sorts_constant_body f))]
    | _ => 
      tmMsg "unrecognized term" ;;
      tmPrint t' ;;
      tmFail "unrecognized term in gather sorts"
    end.

  (* lift the above to a list of packed function/inductive types *)
  Fixpoint gather_sorts_all (xs: list packed) : TemplateMonad (list ( ident * list term)) := 
    match xs with 
    | nil => tmReturn nil
    | (x :: xs')%list => 
      t <- gather_sorts x ;;
      t' <- gather_sorts_all xs' ;;
      tmReturn (t ++ t')%list
    end.

  (* Take a list of argument types and process it for functions/relations:
     for functions, do nothing (signal by returning inl)
     for relations, drop the final return type: later code will replace with a bool return type. Signal by returning inr.
  *)
  Fixpoint conv_fun_rel (tys: list term) : TemplateMonad (list term + list term) :=
    match tys with 
    | [] => tmFail "check_fun_rel on empty type"
    | [x] => 
      if Core.eq_term x t_prop then tmReturn (inr []) else tmReturn (inl [x])
    | x :: xs => 
      r <- conv_fun_rel xs ;; 
      match r with 
      | inl xs' => tmReturn (inl (x :: xs'))
      | inr xs' => tmReturn (inr (x :: xs'))
      end
    end.

  (* given a set of names and unprocessed indices, split into function and relation indices *)
  Definition split_fun_rel (x: ident * list term) : TemplateMonad (ident * (list term + list term)) := 
    r <- conv_fun_rel x.2 ;;
    tmReturn (x.1, r).

  
(* Takes a set of function and relation signatures, as terms, makes sort symbols + interpretation for each of the sorts in the signatures,
   and returns a map (key-value assoc list) from sort terms to sort term symbols.
   
   e.g. if t_prop is in the input, then adds a symbol sort_prop,
        and returns (t_prop, quote sort_prop) in the output map
   *)
  Definition add_sorts_indices (indices: list (list term)) := 
    let sort_ty_terms := uniq_term (concat indices) in 
      (* tmPrint "indices" ;; 
      r <- tmEval all sort_ty_terms ;; 
      tmPrint r ;; *)
      sort_names <- make_names sort_ty_terms ;;
      sort_terms <- add_sorts sort_names ;;
      tmReturn (combine sort_ty_terms sort_terms).


  From MetaCoq.Translations Require Import translation_utils.


  Definition config_level : Universe.t := Universe.of_levels (inr (Level.Level "Config.17")).

  (* extract a universe out of a term or return a default *)
  Definition extr_univ (t: term) : Universe.t := 
    match t with 
    | tSort u => u
    | _ => config_level
    end.

  (* replace a universe level in a term  *)
  Fixpoint rep_sorts_level (univ: Universe.t) (t: term) := 
    match t with 
    | tSort _ => tSort univ
    | tProd x t ts => 
      tProd x (rep_sorts_level univ t) (rep_sorts_level univ ts)
    | tApp f xs => tApp (rep_sorts_level univ f) (map (rep_sorts_level univ) xs)
    | tConstruct ctr idx _ => 
      match Universe.get_is_level univ with 
      | Some lvls => tConstruct ctr idx [lvls]
      | None => t 
      end
    | tInd ind _ => t
      (* match Universe.get_is_level univ with 
      | Some lvls => tInd ind []
      | None => t 
      end *)
    | _ => t
    end.

  (* Generate sorts, sort interpretation, and function symbols for an 
     input list of either top-level function definitions, or top-level inductive definitions.
     For inductive definitions, treat the constructors of the inductive as function definitions.
     Generates syntax and semantics for the types of the input functions (but does not examine their bodies).
  *)

  Definition get_ind_ctors (i: inductive) (u: Instance.t) : TemplateMonad (list term) :=
    x' <- tmQuoteInductive i.(inductive_mind) ;;
    match nth_error x'.(ind_bodies) i.(inductive_ind) with 
    | None => tmFail "get_ind_ctors"
    | Some bod => 
      tmReturn (map_with_index (make_ind_ctor i u) bod.(ind_ctors))
    end.

  Definition get_orig_funs (x: packed) : TemplateMonad (list (term)) := 
    x <- tmQuotePacked x ;;
    match x with 
    | tApp (tInd ind u) args => 
      tst <- is_prop_ind ind ;; 
      if (tst: bool)
      then tmReturn [x]
      else 
        ctors <- get_ind_ctors ind u ;;
        tmReturn (map (fun ctor => tApp ctor args) ctors)
    | tInd ind u => 
      tst <- is_prop_ind ind ;; 
      if (tst: bool)
      then tmReturn [x]
      else get_ind_ctors ind u 
    | _ => tmReturn [x]
    end.

  Fixpoint split_sum_list {A B C} (xs: list (A * (B + C))) : list (A * B) * list (A * C) := 
    match xs with 
    | [] => ([], [])
    | (k, x) :: xs' => 
      let '(ls, rs) := split_sum_list xs' in 
      match x with 
      | inl x' => ((k, x') :: ls, rs)
      | inr x' => (ls, (k, x') :: rs)
      end
    end.

  

  Record translation_table := {
    mp_srts : list (term * term) ; (* map from original sorts to new sort constructors, e.g. quote Z |-> quote (sort_Z) *)
    mp_funs : list (term * term) ; (* map from original funs to new fun constructors, e.g. quote rev |-> quote (rev_f) *)
    mp_rels : list (term * term) ; (* map from original rels to new rel constructors, e.g. quote In |-> quote (In_r) *)
    mp_consts: list (term * smt_fun_base) ; (* map from added constant terms to corresponding smt constants e.g. quote z_const_f |-> IntLit *)
  }.

  Definition all_symbs (t: translation_table) := List.app t.(mp_funs) t.(mp_rels).

  

  (* Main automation function. Given a quoted term for Type, a list of packed functions/inductives, and a list of packed relations/inductives, 
    add syntax and semantics for sorts,
    syntax for functions and relations,
    and return a translation table recording a map from the quoted sorts/functions/constructors to the new syntaxes.
    *)

  Definition add_funs (typ_term: term) (funs: list packed) (rels: list packed) : TemplateMonad translation_table := 
    names_indices <- gather_sorts_all (List.app funs rels) ;;
    (* tmPrint "names_indices:" ;;  *)
    (* to_print <- tmEval all names_indices ;;
    tmPrint to_print ;;  *)
    names_funs_rels <- fmap split_sum_list (mapM split_fun_rel names_indices) ;; 

    let '(names_funs, fun_indices) := List.split names_funs_rels.1 in 
    let '(names_rels, rel_indices) := List.split names_funs_rels.2 in 

    sorted_indices <- add_sorts_indices (fun_indices ++ rel_indices ++ [[t_prop]]) ;; 
    let consts := gather_consts sorted_indices in 

    srts <- tmLocate1 "sorts" ;;
    srt <- tmUnquoteTyped Type (monomorph_globref_term srts) ;;
    add_interp_sorts (fst (split sorted_indices)) srt ;;

    arg_term <- tmQuote (list srt) ;;
    ret_term <- tmQuote srt ;;
    funs_ty_term <- tmQuote (list srt -> srt -> Type) ;;
    rels_ty_term <- tmQuote (list srt -> Type) ;;
    nil_term <- tmQuote (@nil srt) ;;

    idx' <- unquote_fun_indices srt (map (map (subst_terms sorted_indices)) fun_indices) ;;
    idx'' <- quote_fun_indices srt idx' ;;
    let (r, consts_builder) := funs_body nil_term arg_term ret_term names_funs idx'' (rep_sorts_level (extr_univ typ_term) funs_ty_term) consts  in 
    tmMkInductive' r ;;
    tmMsg "added function symbol inductive fol_funs" ;;

    idx' <- unquote_rel_indices srt (map (map (subst_terms sorted_indices)) rel_indices) ;;
    idx'' <- quote_rel_indices srt idx' ;;
    tmMkInductive' (rel_body arg_term names_rels idx'' (rep_sorts_level (extr_univ typ_term) rels_ty_term) ) ;;
    tmMsg "added relation symbol inductive fol_rels" ;;

    funs' <- tmLocate1 "fol_funs" ;;
    rels' <- tmLocate1 "fol_rels" ;;
    match funs', rels' with 
    | IndRef ind_f, IndRef ind_r => 
      x <- tmQuoteInductive ind_f.(inductive_mind) ;;
      y <- tmQuoteInductive ind_r.(inductive_mind) ;;
      match x.(ind_bodies), y.(ind_bodies) with 
      | [x'], [y'] => 
        orig_funs <- mapM get_orig_funs funs ;;
        orig_rels <- mapM get_orig_funs rels ;;
        tmReturn {|
          mp_srts := sorted_indices ;
          mp_funs := List.combine (concat orig_funs) (map_with_index (make_ind_ctor ind_f []) x'.(ind_ctors)) ;
          mp_rels := List.combine (concat orig_rels) (map_with_index (make_ind_ctor ind_r []) y'.(ind_ctors)) ;
          mp_consts := consts_builder ind_f ;
        |}

      | _ , _ => tmFail "unexpected size of funs/rels  inductive"
      end
    | _, _ => tmFail "error making funs"
    end.


  Variable (srts: Type).
  Variable (interp_srts : srts -> Type).
  Variable (fol_funs : list srts -> srts -> Type).
  Variable (fol_rels : list srts -> Type).
  
  Fixpoint denote_func_type
    (args: list srts)
    (ret: srts)
  :
    Type
  := 
    match args with 
    | nil => interp_srts ret
    | (t :: ts)%list => (interp_srts t -> (denote_func_type ts ret))%type
    end.

  Fixpoint denote_rel_type
    (args: list srts)
  :
    Type
  := 
    match args with 
    | nil => Prop
    | (t :: ts)%list => (interp_srts t -> (denote_rel_type ts))%type
    end.

  (* Version of apply_denote_func that works with hlists because that is how
      arguments are supplied when interpreting functions. *)
  Equations apply_denote_func
    {arg_tys: list srts}
    (ret_ty: srts)
    (args: HList.t interp_srts arg_tys)
    (f: denote_func_type arg_tys ret_ty)
  :
    interp_srts ret_ty
  := {
    @apply_denote_func nil _ _ v => v;
    @apply_denote_func (t :: ts) _ (arg ::: args) f =>
      apply_denote_func ret_ty args (f arg);
  }.

  Equations apply_denote_rel
    {arg_tys: list srts}
    (args: HList.t interp_srts arg_tys)
    (f: denote_rel_type arg_tys)
  :
    Prop
  := {
    @apply_denote_rel nil _ v => v;
    @apply_denote_rel (t :: ts) (arg ::: args) r =>
      apply_denote_rel args (r arg);
  }.

  Definition gen_const_denote_case (const_entry : (term * smt_fun_base)) : branch term := 
    match const_entry.2 with 
    | IntLit => {| bcontext := [nNamed "z"]; bbody := tRel 0 |}
    | BoolLit => {| bcontext := [nNamed "b"]; bbody := tRel 0 |}
    | _ => {| bcontext := [nNamed "x"]; bbody := tRel 0 |}
    end.

  Definition gen_denote_func_cases (tbl: translation_table) : list (branch term) :=
    map (fun '(f, _) => {| bcontext := nil; bbody := f |})
              tbl.(mp_funs)
    ++
    map gen_const_denote_case tbl.(mp_consts).

  Definition gen_denote_rel_cases (tbl: translation_table) : list (branch term) :=
    List.map (fun '(f, _) => {| bcontext := nil; bbody := f |})
              tbl.(mp_rels).

  Definition make_denote_f q_list_srts q_srts q_fol_funs fol_funs_ref q_denote_func_type tbl := 
    (tLambda
      (nNamed "arg_tys")
      q_list_srts
      (tLambda
        (nNamed "ret_ty")
        q_srts
        (tLambda
          (nNamed "f")
          (tApp q_fol_funs [tRel 1; tRel 0])
          (tCase
            {|
              ci_ind := fol_funs_ref;
              ci_npar := 0;
              ci_relevance := Relevant
            |}
            {|
              puinst := nil;
              pparams := nil;
              pcontext := [nNamed "s"; nNamed "s"; nNamed "l"];
              preturn :=
                tApp
                  q_denote_func_type
                  [tRel 2; tRel 1]
            |}
            (tRel 0)
            (gen_denote_func_cases tbl)
          )
        )
      )
    ).

  Definition make_interp_fun q_list_srts q_srts q_hargs q_fol_funs q_apply_denote_func q_denote_func := 
    (tLambda
     {|
       binder_name := BasicAst.nNamed "arg_tys"; binder_relevance := Relevant
     |}
     q_list_srts
     (tLambda
        {|
          binder_name := BasicAst.nNamed "ret_ty";
          binder_relevance := Relevant
        |} q_srts
        (tLambda
           {|
             binder_name := BasicAst.nNamed "f"; binder_relevance := Relevant
           |} (tApp q_fol_funs [tRel 1; tRel 0])
           (tLambda
              {|
                binder_name := BasicAst.nNamed "hargs";
                binder_relevance := Relevant
              |}
              (tApp q_hargs [tRel 2])
              (tApp
                 q_apply_denote_func
                 [tRel 3; tRel 2; tRel 0;
                 tApp q_denote_func [tRel 3; tRel 2; tRel 1]]))))).

  Definition gen_interp_funs (tbl: translation_table) :=
    q_list_srts <- tmQuote (list srts) ;;
    q_srts <- tmQuote srts ;;
    q_fol_funs <- tmQuote fol_funs ;;
    fol_funs_ref <- match q_fol_funs with
                    | tInd r _ => tmReturn r
                    | _ => tmFail "fol_funs_ref"
                    end ;;
    q_denote_func_type <- tmQuote denote_func_type ;;

    let denote_funs := make_denote_f q_list_srts q_srts q_fol_funs fol_funs_ref q_denote_func_type tbl in
    q_hargs <- tmQuote (fun x => HList.t interp_srts x) ;;
    q_apply_denote_func <- tmQuote (@apply_denote_func) ;;
    denote_funs <- tmEval all denote_funs ;;
    (* tmPrint "denote_funs:" ;; 
    tmPrint denote_funs ;;
    tmPrint "unquoted:" ;; 
    denote_funs_unquoted <- tmUnquote denote_funs ;;
    tmPrint denote_funs_unquoted ;; *)
    rhs <- tmEval all (make_interp_fun q_list_srts q_srts q_hargs q_fol_funs q_apply_denote_func denote_funs) ;;
    (* tmPrint "rhs:" ;; 
    tmPrint rhs ;; *)
    tmMkDefinition "interp_funs" rhs.
    

  Definition make_denote_r q_list_srts q_fol_rels fol_rels_ref q_denote_rel_type tbl := 
    (tLambda
      (nNamed "arg_tys")
      q_list_srts
      (tLambda
        (nNamed "f")
        (tApp q_fol_rels [tRel 0])
        (tCase
          {|
            ci_ind := fol_rels_ref;
            ci_npar := 0;
            ci_relevance := Relevant
          |}
          {|
            puinst := nil;
            pparams := nil;
            pcontext := [nNamed "s"; nNamed "l"];
            preturn :=
              tApp
                q_denote_rel_type
                [tRel 1]
          |}
          (tRel 0)
          (gen_denote_rel_cases tbl)
        )
      )
    ).

  Definition make_interp_rel q_list_srts q_hargs q_fol_rels q_apply_denote_rel q_denote_rel := 
    (tLambda
      {|
        binder_name := BasicAst.nNamed "arg_tys"; binder_relevance := Relevant
      |}
      q_list_srts
      (tLambda
        {|
          binder_name := BasicAst.nNamed "r"; binder_relevance := Relevant
        |} (tApp q_fol_rels [tRel 0])
        (tLambda
          {|
            binder_name := BasicAst.nNamed "hargs";
            binder_relevance := Relevant
          |}
          (tApp q_hargs [tRel 1])
          (tApp
              q_apply_denote_rel
              [tRel 2; tRel 0;
              tApp q_denote_rel [tRel 2; tRel 1]])))).

  Definition gen_interp_rels (tbl: translation_table) :=
    q_list_srts <- tmQuote (list srts) ;;
    q_fol_rels <- tmQuote fol_rels ;;
    fol_rels_ref <- match q_fol_rels with
                    | tInd r _ => tmReturn r
                    | _ => tmFail "fol_rels_ref"
                    end ;;
    q_denote_rel_type <- tmQuote denote_rel_type ;;

    let denote_rels := make_denote_r q_list_srts q_fol_rels fol_rels_ref q_denote_rel_type tbl in
    q_hargs <- tmQuote (fun x => HList.t interp_srts x) ;;
    q_apply_denote_rel <- tmQuote (@apply_denote_rel) ;;
    tmMkDefinition "interp_rels" (make_interp_rel q_list_srts q_hargs q_fol_rels q_apply_denote_rel denote_rels).


  (* helper functions for autogenerating boolean term tests *)


  Definition app_extract_ctor t := 
    tApp 
    (tConst (MPfile ["Core"; "Reflection"; "MirrorSolve"]%list, "extract_ctor") [])
      [t].

  Definition mk_test_lambda_strict (x: term) : term := 
    tLambda {| binder_name := BasicAst.nNamed "t"; binder_relevance := Relevant |}
  (tInd
    {|
        inductive_mind := (MPfile ["Ast"; "Template"; "MetaCoq"]%list, "term");
        inductive_ind := 0
      |} nil)
    (tApp (tConst (MPfile ["Core"; "Reflection"; "MirrorSolve"]%list, "eq_prefix")
          nil)
        [tRel 0; x]).

  Definition mk_test_lambda_ctor (x: term) : term := 
    tLambda {| binder_name := BasicAst.nNamed "t"; binder_relevance := Relevant |}
  (tInd
	 {|
       inductive_mind := (MPfile ["Ast"; "Template"; "MetaCoq"]%list, "term");
       inductive_ind := 0
     |} nil)
  (tApp (tConst (MPfile ["Datatypes"; "Init"; "Coq"]%list, "orb") nil)
     [tApp
        (tConst
           (MPfile ["Core"; "Reflection"; "MirrorSolve"]%list, "eq_ctor")
           nil)
        [tRel 0; app_extract_ctor x];
     tApp
       (tConst (MPfile ["Core"; "Reflection"; "MirrorSolve"]%list, "eq_term")
          nil)
       [tRel 0; x]]).

  Definition mk_test_plain (name: ident) (t: term) := 
    t' <- tmQuote t ;;
    let name' := ("is_" ++ name ++ "_t") in 
    tmMkDefinition name' (mk_test_lambda_ctor t').

  Definition mk_test (name: ident) (t: packed) := 
    match t with 
    | pack x =>
      t' <- tmQuote2 x ;;
      let name' := ("is_" ++ name ++ "_t") in 
      tmMkDefinition name' (mk_test_lambda_ctor t') ;;
      tmMsg ("added definition for " ++ name')
    end.
    
  (* Add boolean term tests for a list of input definitions. 
    Names using the Coq name of the definition.  
    *)
  Definition add_test (x: term) := 
    match x with 
    | tConst name _ => 
      mk_test_plain (snd name) x
    | tConstruct ind idx _ => 
      inds <- tmQuoteInductive ind.(inductive_mind) ;;
      match nth_error inds.(ind_bodies) ind.(inductive_ind)  with 
      | Some ind' =>
        match nth_error ind'.(ind_ctors) idx with 
        | Some ctor => 
          mk_test_plain ctor.(cstr_name) x
        | None => tmFail "incorrect index into ctors??"
        end
      | None => tmFail "incorrect index into inds??"
      end
    | _ => 
      tmPrint t ;;
      tmFail "unhandled term for getting name in add_test"
    end.

  Definition add_test_packed x := 
    tmQuotePacked x >>= add_test.

  Definition add_tests xs := 
    mapM add_test xs.

  Definition add_tests_packed xs :=
    mapM add_test_packed xs.

  Definition tmUnquoteTypedId (A: Type) (id: ident) : TemplateMonad A :=
    typed_tm <- tmLocate1 id ;;
    tmUnquoteTyped A (monomorph_globref_term typed_tm).

  (* Helper function for generating a signature, given sorts, funs, and rels. *)
  Definition gen_sig'
    (sort_type : term)
    (fun_type: term)
    (rel_type: term)
  :
    TemplateMonad ident
  :=
    builder <- tmQuote Build_signature ;;
    builder' <- tmEval all builder ;;
    (* tmMsg "builder:" ;;
    tmPrint builder' ;; *)
    id <- tmFreshName "sig" ;;
    tmMkDefinition id (tApp builder [sort_type; fun_type; rel_type]) ;;
    tmReturn id
    (* tmUnquoteTypedId signature id *)
  .

  Definition gen_sig
    (typ_term: term)
    (sorts : Type)
    (funs: arity sorts -> sorts -> Type)
    (rels: arity sorts -> Type)
  :
    TemplateMonad ident
  :=
    arg_sorts <- tmQuote sorts ;;
    arg_funs <- tmQuote funs ;;
    arg_rels <- tmQuote rels ;;
    gen_sig' arg_sorts arg_funs arg_rels
  .


  Require MirrorSolve.FirstOrder.
  Require MirrorSolve.Reflection.Tactics.

  (* Unquote a term as a function symbol. This is tricky because the type of the function symbol is dependent,
    so we make use of several holes for the argument and return sorts.
    Magically it works out!!
  *)
  Definition coerce_tac_syn_f {s: FirstOrder.signature} {m: FirstOrder.model s} (t: term)  : TemplateMonad (Tactics.tac_syn s m) := 
    a <- tmUnquoteTyped (list (s.(sig_sorts))) hole ;;
    r <- tmUnquoteTyped (s.(sig_sorts)) hole ;;
    fs <- tmUnquoteTyped (s.(sig_funs) a r) t ;;
    tmReturn (Tactics.tac_fun s fs).
  Definition coerce_tac_syn_r {s: FirstOrder.signature} {m: FirstOrder.model s} (t: term)  : TemplateMonad (Tactics.tac_syn s m) := 
    a <- tmUnquoteTyped (list (s.(sig_sorts))) hole ;;
    rs <- tmUnquoteTyped (s.(sig_rels) a) t ;;
    tmReturn (Tactics.tac_rel s rs).

  Definition build_fun_match {s: FirstOrder.signature} {m: FirstOrder.model s} (orig: term) (symb: term) : TemplateMonad ((term -> bool) * Tactics.tac_syn s m) :=
    x <- tmQuote orig ;;
    test <- tmUnquoteTyped (term -> bool) (mk_test_lambda_strict x) ;;
    tac <- coerce_tac_syn_f symb ;;
    tmReturn (test, tac).
  Definition build_rel_match {s: FirstOrder.signature} {m: FirstOrder.model s} (orig: term) (symb: term) : TemplateMonad ((term -> bool) * Tactics.tac_syn s m) :=
    x <- tmQuote orig ;;
    test <- tmUnquoteTyped (term -> bool) (mk_test_lambda_strict x) ;;
    tac <- coerce_tac_syn_r symb ;;
    tmReturn (test, tac).

  Definition build_sort_match {s: FirstOrder.signature} {m: FirstOrder.model s} (orig: term) (symb: term) : TemplateMonad ((term -> bool) * s.(sig_sorts)) := 
    x <- tmQuote orig ;;
    test <- tmUnquoteTyped (term -> bool) (mk_test_lambda_strict x) ;;
    srt <- tmUnquoteTyped s.(sig_sorts) symb ;;
    tmReturn (test, srt).

    
  (* MetaCoq Run (
    let r := (make_lit_wf sig fm_model sort_Z z_const_f) in
    r_term <- tmQuote r ;;
    tmMkDefinition "z_lit_wf" r_term ;; 
    tmLocate1 "z_lit_wf" >>= tmExistingInstance
  ). *)

  Definition add_const_wf_instance (s: FirstOrder.signature) (m: FirstOrder.model s) (const_f_t : term) (const_ty : smt_fun_base) : TemplateMonad unit :=
    srt <- tmUnquoteTyped s.(sig_sorts) hole ;;
    ret <- tmUnquoteTyped s.(sig_sorts) hole ;;
    match const_ty with 
    | IntLit =>
      f <- tmUnquoteTyped (BinNums.Z -> s.(sig_funs) [] ret) const_f_t ;;
      r_term <- tmQuote (Tactics.z_wf s m ret f) ;;
      tmMkDefinition "z_lit_wf" r_term ;;
      tmLocate1 "z_lit_wf" >>= tmExistingInstance
    | BoolLit =>
      f <- tmUnquoteTyped (bool -> s.(sig_funs) [] ret) const_f_t ;;
      r_term <- tmQuote (Tactics.b_wf s m ret f) ;;
      tmMkDefinition "b_lit_wf" r_term ;;
      tmLocate1 "b_lit_wf" >>= tmExistingInstance
    | _ => 
      tmPrint const_ty ;;
      tmFail "unimplemented const_wf_instance"
    end.

  Definition add_const_wf_instances (s: FirstOrder.signature) (m: FirstOrder.model s) (t: translation_table) : TemplateMonad unit := 
   mapM (fun '(const_f_t, const_ty) => add_const_wf_instance s m const_f_t const_ty) t.(mp_consts) ;;
   tmReturn tt.

  Definition build_const_match (s: FirstOrder.signature) (m: FirstOrder.model s) (const_term : term) (const_ty : smt_fun_base) : TemplateMonad ((term -> bool) * Tactics.tac_syn s m) := 
    match const_ty with
    | IntLit => 
      wf_inst <- tmInferInstance None (Tactics.LitWF s m Tactics.z_lit) ;;
      match wf_inst with 
      | my_Some x => 
        tmReturn (Tactics.is_z_term, @Tactics.tacLit s m Tactics.z_lit x)
      | my_None => 
        tmPrint const_ty ;;
        tmFail "couldn't find a wf instance for int literal"
      end
    | BoolLit => 
      wf_inst <- tmInferInstance None (Tactics.LitWF s m Tactics.bool_lit) ;;
      match wf_inst with 
      | my_Some x => 
        tmReturn (Tactics.is_bool_term, @Tactics.tacLit s m Tactics.bool_lit x)
      | my_None => 
        tmPrint const_ty ;;
        tmFail "couldn't find a wf instance for bool literal"
      end
    | _ => 
      tmPrint const_ty ;;
      tmFail "unimplemented tactic type"
    end.


  Definition add_symb_matches (s: FirstOrder.signature) (m: FirstOrder.model s) (t: translation_table) : TemplateMonad unit := 
    fun_matches <- mapM (fun '(orig_f, sym_f) => @build_fun_match s m orig_f sym_f) t.(mp_funs) ;;
    rel_matches <- mapM (fun '(orig_r, sym_r) => @build_rel_match s m orig_r sym_r) t.(mp_rels) ;;
    const_matches <- mapM (fun '(const_f, const_ty) => @build_const_match s m const_f const_ty) t.(mp_consts) ;;
    matches_term <- tmQuote (List.app fun_matches (List.app rel_matches const_matches)) ;;
    tmMkDefinition "match_tacs" matches_term.

  Definition add_sort_matches (s: FirstOrder.signature) (m: FirstOrder.model s) (t: translation_table) : TemplateMonad unit := 
    sort_matches <- mapM (fun '(orig, sym) => @build_sort_match s m orig sym) t.(mp_srts) ;;
    matches_term <- tmQuote sort_matches ;;
    tmMkDefinition "match_sorts" matches_term.

  (* Given a signature, model, and translation table, add boolean term matches for elements in the translation table. 
     The definitions are saved to "match_tacs" for funs/rels and "match_sorts" for sorts.
   *)
  Definition add_matches (s: FirstOrder.signature) (m: FirstOrder.model s) (t: translation_table) : TemplateMonad unit := 
    add_symb_matches s m t ;;
    add_sort_matches s m t.

  Definition print_sort_base (sb: smt_sort_base) : ident := 
    match sb with 
    | SInt => "Int"
    | SBool => "Bool"
    | SBitVector => "unimplemented--BV"
    | SCustom s => String.of_string s
    end.


  Fixpoint subst_tys (env: list smt_ind_base) (rec_name: ident) (x: term) {struct x} : option ident := 
    match x with 
    | tInd ind _ => 
      match ind.(inductive_ind) with 
      | 0 => Some ind.(inductive_mind).2
      | _ => None
      end
    | tApp f es => 
      match subst_tys env rec_name f with 
      | Some f' => 
        let opt_args := map (subst_tys env rec_name) es in 
        match map_option_all (fun x => x) opt_args with
        | Some es' => 
          Some (f' ++ "_" ++ str_join es' "_")
        | None => None
        end
      | None => None
      end
    | tRel x => 
      match nth_error env x with 
      | Some SIRec => Some rec_name 
      | Some (SISort x) => Some (print_sort_base x)
      | _ => None
      end
    | _ => None
    end.
  
  (* helper functions for building an smt_sig theory from a translation table *)

  (* Convert a basic (not inductive or product) type to a smt type.
     Generally types can be products so the translation uses a typing environment env.
  *)
  Definition translate_cstr_type_base (env: list smt_ind_base) (rec_name : ident) (x: term) :  TemplateMonad smt_ind_base := 
    let ret := 
      match x with 
      | tVar nme => Some (SISort (SCustom (String.to_string nme)))
      | tRel v => nth_error env v
      | tApp _ _ => 
        match subst_tys env rec_name x with 
        | Some nme => 
          Some (SISort (SCustom (String.to_string nme)))
        | None => None
          (* tmPrint x ;; 
          tmFail "failed to print type name for custom sort in translate_cstr_type_base"  *)
        end
      | _ => None
        (* tmPrint x ;;
        tmFail "unhandled term in translate_cstr_type_base" *)
      end in 
    match ret with 
    | Some r => tmReturn r
    | None => 
      if is_z_srt x then 
        tmReturn (SISort SInt)
      else if orb (Core.eq_term x t_prop) (Core.eq_term x t_bool) then 
        tmReturn (SISort SBool)
      else
        tmPrint "unhandled type?" ;;
        tmPrint x ;;
        env <- tmEval all env ;;
        tmPrint "env:" ;;
        tmPrint env ;;
        tmFail "weird error in translate_cstr_type_base"
    end.
      

  (* Translate a nested type (including products) into a list of types,
     adding bound types to the environment as it goes.
      e.g. Int -> Int -> Bool |-> [SInt; SInt; SBool]
  *)
  Fixpoint translate_cstr_type (env: list smt_ind_base) (rec_name: ident) (x: term) : TemplateMonad (list smt_ind_base) := 
    match x with 
    | tProd _ ty bod => 
      ty' <- translate_cstr_type_base env rec_name ty ;; 
      r <- translate_cstr_type (ty' :: env) rec_name bod ;;
      tmReturn (ty' :: r)
    | _ =>
      inner <- translate_cstr_type_base env rec_name x ;; 
      tmReturn [inner]
    end.

  (* Translate the type of an inductive constructor to a list of correpsonding smt_types.
     Drop the final element of the resulting type (which will always be SIRec, i.e. the parent inductive)
     because it is implicit in the definition of smt_ind.

     Drop the prefix of constructors that corresponds to the parameters of the parent inductive type (which are passed through env).
   *)

   Fixpoint drop_param_prefix (n: nat) (t: term) := 
    match n, t with 
    | 0, _ => Some t
    | S n', tProd _ _ t' => (* TODO: validate that the binder is actually over a type here *)
      drop_param_prefix n' t'
    | _, _ => None
    end.

  Definition translate_constructor_body (env: list smt_ind_base) (rec_name: ident) (suffix: ident) (ctor: constructor_body) : TemplateMonad (string * list smt_ind_base) := 
    match drop_param_prefix (length env) ctor.(cstr_type) with 
    | Some t =>   
      inner <- translate_cstr_type (List.rev (SIRec :: env)) rec_name t ;; 
      tmReturn (String.to_string (ctor.(cstr_name) ++ suffix), drop_last inner )
    | None => 
      tmPrint "environment:" ;;
      tmPrint env ;;
      tmPrint "constructor type:" ;;
      tmPrint ctor.(cstr_type) ;;
      tmFail "couldn't monomorphize constructor type + environment"
    end.

  Definition translate_smt_ind (x: inductive) (env: list smt_ind_base) (suffix: ident) : TemplateMonad smt_ind := 
    ind <- tmQuoteInductive x.(inductive_mind) ;; 
    match ind.(ind_bodies) with 
    | [v] => 
      cases <- mapM (translate_constructor_body env x.(inductive_mind).2 suffix) v.(ind_ctors) ;;
      tmReturn (SICases cases)
    | _ => tmFail "unhandled mutual inductive in translate_smt_ind"
    end.

  Definition make_ind_custom (x: term) : TemplateMonad smt_sort_base := 
    if is_z_srt x then 
      tmReturn (SInt)
    else if orb (Core.eq_term x t_prop) (Core.eq_term x t_bool) then 
      tmReturn (SBool)
    else
      get_ty_name x >>= liftM (fun s => SCustom (String.to_string s)).


  (* package the functions above into a clean Type |-> smt_sort conversion function *)
  Definition translate_smt_sort (x: term) : TemplateMonad smt_sort := 
    if orb (Core.eq_term x t_prop) (Core.eq_term x t_bool) then 
      tmReturn (SortBase SBool)
    else if is_z_srt x then 
      tmReturn (SortBase SInt)
    else 
      match x with 
      | tVar nme => tmReturn (SortBase (SCustom (String.to_string nme)))
      | tInd ind _ => 
        r <- translate_smt_ind ind [] "" ;;
        let name := String.to_string ind.(inductive_mind).2 in 
          tmReturn (SortInd name r)
      | tApp (tInd ind _) args => 
        inner <- mapM make_ind_custom args ;;
        inner_cnames <- mapM get_global_name args ;;
        r <- translate_smt_ind ind (map SISort inner) ("_" ++ str_join inner_cnames "_" ) ;;
        name <- get_ty_name x ;;
        let name := String.to_string name in 
          tmReturn (SortInd name r) 
      | _ => 
        tmPrint x ;;
        tmFail "unrecognized sort in translate_smt_sort"
      end.

  Require Import MirrorSolve.SMTSig.

  Definition translate_one_sort_binding (s: signature) (kv: term * term) : TemplateMonad (s.(sig_sorts) * smt_sort) := 
    srt_symb <- tmUnquoteTyped s.(sig_sorts) kv.2 ;; 
    smt_srt <- translate_smt_sort kv.1 ;; 
    tmReturn (srt_symb, smt_srt).

  Definition translate_one_fun (s: signature) (x: term * term) : TemplateMonad (packed_sfun s * smt_fun) := 
    args <- tmUnquoteTyped (list s.(sig_sorts)) hole ;;
    ret <- tmUnquoteTyped s.(sig_sorts) hole ;;
    f <- tmUnquoteTyped (s.(sig_funs) args ret) x.2 ;; 
    name <- (get_global_name x.1) >>= liftM String.to_string ;;
    match x.1 with 
    | tApp (tConst _ _) _ 
    | tConst _ _ => 
      tmReturn (SMTSig.PSF s _ _ f, FUninterp name)

    | tConstruct _ _ _
    | tApp (tConstruct _ _ _) _ => 
      tmReturn (SMTSig.PSF s _ _ f, FPrim (F_sym name))

    | tApp (tVar _) _ 
    | tVar _ => 
      tmReturn (SMTSig.PSF s _ _ f, FUninterp name)
      
    | _ => 
      tmPrint "don't know how to handle term:" ;;
      r <- tmEval all x.1 ;;
      tmPrint r ;; 
      tmFail "unexpected term in translate_one_fun"
    end.

  Definition translate_override_fun (s: signature) (x: term * String.string) : TemplateMonad (packed_sfun s * smt_fun) := 
    args <- tmUnquoteTyped (list s.(sig_sorts)) hole ;;
    ret <- tmUnquoteTyped s.(sig_sorts) hole ;;
    f <- tmUnquoteTyped (s.(sig_funs) args ret) x.1 ;; 
    tmReturn (SMTSig.PSF s _ _ f, FPrim (F_sym x.2)).

  Definition translate_one_rel (s: signature) (sort_prop : s.(sig_sorts)) (x: term * term) : TemplateMonad (packed_sfun s * smt_fun) := 
      args <- tmUnquoteTyped (list s.(sig_sorts)) hole ;;
      f <- tmUnquoteTyped (s.(sig_rels) args) x.2 ;; 
      name <- (get_global_name x.1) >>= liftM String.to_string ;;
      match x.1 with 
      | tApp (tConst _ _) _
      | tConst _ _ => 
        tmReturn (SMTSig.PSR s _ sort_prop f, FUninterp name)

      | tApp (tInd _ _) _
      | tInd _ _ => 
        tmReturn (SMTSig.PSR s _ sort_prop f, FUninterp name)

      | tApp (tVar _) _ 
      | tVar _ => 
        tmReturn (SMTSig.PSR s _ sort_prop f, FUninterp name)
        
      | _ => 
        tmPrint "don't know how to handle term:" ;;
        tmPrint x.1 ;; 
        tmFail "unexpected term in translate_one_rel"
      end.

  Definition translate_override_rel (s: signature) (sort_prop : s.(sig_sorts)) (x: term * String.string) : TemplateMonad (packed_sfun s * smt_fun) := 
    args <- tmUnquoteTyped (list s.(sig_sorts)) hole ;;
    f <- tmUnquoteTyped (s.(sig_rels) args) x.1 ;; 
    tmReturn (SMTSig.PSR s _ sort_prop f, FPrim (F_sym x.2)).

  Definition translate_const (s: signature) (x: term * smt_fun_base) : TemplateMonad (packed_sfun s * smt_fun) := 
    args <- tmUnquoteTyped (list s.(sig_sorts)) hole ;;
    ret <- tmUnquoteTyped s.(sig_sorts) hole ;;
    match x.2 with 
    | BoolLit => 
      f <- tmUnquoteTyped (forall (b: bool), s.(sig_funs) args ret) x.1 ;;
      tmReturn (SMTSig.PSL s _ _ _ f, FPrim x.2)
    | IntLit => 
      f <- tmUnquoteTyped (forall (z: BinNums.Z), s.(sig_funs) args ret) x.1 ;;
      tmReturn (SMTSig.PSL s _ _ _ f, FPrim x.2)
    | _ => 
      tmPrint x.2 ;; 
      tmPrint x.1 ;; 
      tmFail "unhandled literal type in translate_const"
    end.


  Definition unpack_pair (x: packed * String.string) : TemplateMonad (term * String.string) := 
    r <- tmQuotePacked x.1 ;; 
    tmReturn (r, x.2).

  Definition partition_mp (mp: list (term * term)) (overrides : list (term * String.string)) : (list (term * term)) * (list (term * String.string)) := 
    let override_terms := map fst overrides in 
    let orig := remove_all _ _ Core.eq_term override_terms mp in 
    let news := find_all _ _ Core.eq_term override_terms mp in 
    let new_with_name := join (eqb := Core.eq_term) news overrides in 
    (orig, map (fun '(x, (y, z)) => (y, z)) new_with_name).


  (* Build a printing ctx (smt_sig) for a signature and translation table, 
     using a list of function symbol overrides 
  *)
  Definition build_printing_ctx (s: signature) (sort_prop: s.(sig_sorts)) (tbl: translation_table) (overrides : list (packed * String.string)) : TemplateMonad (smt_sig s) := 
    srts <- mapM (translate_one_sort_binding s) tbl.(mp_srts) ;; 
    overrides <- mapM unpack_pair overrides ;;
    let (norm_funs, over_funs) := partition_mp tbl.(mp_funs) overrides in 
    let (norm_rels, over_rels) := partition_mp tbl.(mp_rels) overrides in
    funs <- mapM (translate_one_fun s) norm_funs ;;
    rels <- mapM (translate_one_rel s sort_prop) norm_rels ;;
    funs_over <- mapM (translate_override_fun s) over_funs ;; 
    rels_over <- mapM (translate_override_rel s sort_prop) over_rels ;;
    consts <- mapM (translate_const s) tbl.(mp_consts) ;; 
    tmReturn (MkSMTSig s srts (funs ++ funs_over ++ rels ++ rels_over ++ consts)).

End Config.

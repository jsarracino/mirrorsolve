From MetaCoq.Template Require Import All Loader.
Import MCMonadNotation.

Require Import Coq.Strings.String.

Require Import Coq.Lists.List.
Open Scope bs.

Universe sorts_level.

Definition map_with_index {A B} (f: nat -> A -> B) (xs: list A) : list B := 
  (fix rec xs acc :=
    match xs with 
    | nil => nil
    | x :: xs' => f acc x :: rec xs' (S acc)
    end
  ) xs 0.

Require MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Utils.

Definition inc_var : term * term -> term * term := fun '(k, v) => 
  match k with 
  | tRel n => (tRel (S n), v)
  | _ => (k, v)
  end.

Fixpoint subst_terms (env: list (term * term)) (t: term) := 
  match find _ _ Core.eq_term t env with 
  | Some t' => t'
  | None => 
    match t with 
    | tApp f args => 
      tApp (subst_terms env f) (map (subst_terms env) args)
    | tProd x ty bod => 
      tProd x (subst_terms env ty) (subst_terms (map inc_var env) bod)
    | _ => t 
    end
  end.

Polymorphic Fixpoint mapM {A B} (f: A -> TemplateMonad B) (xs: list A) : TemplateMonad (list B) :=
  match xs with 
  | nil => tmReturn nil
  | a :: xs' => 
    x <- f a ;;
    r <- mapM f xs' ;;
    tmReturn (x :: r)
  end.

Polymorphic Definition liftM {A B} (f: A -> B) : A -> TemplateMonad B := 
  fun a => tmReturn (f a).

Polymorphic Definition tmQuote2 {X} (x: X) := 
  tmQuote x >>= tmQuote.

Section Config.

  Set Universe Polymorphism.

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

  Definition mk_sorts_ctor (ind: inductive) (u: Instance.t) (i: nat) (name: ident) : term := 
    tConstruct ind i u.

  Definition add_sorts (names: list ident) : TemplateMonad (list term) := 
    tmMkInductive' (sorts_body names) ;;
    tmPrint "added inductive definition for sorts" ;;
    srts <- tmLocate "sorts" ;; 
    match srts with 
    | nil => tmFail "new sort not named sorts"
    | (IndRef i) :: _ => tmReturn (map_with_index (mk_sorts_ctor i []) names)
    | _ => tmFail "sorts is not an inductive!"
    end.

  Definition make_interp_branch (r: term) : branch term :=  {|
    bcontext := [];
    bbody := r
  |}.

  Definition packed := {T & T}.
  Notation pack x := (existT _ _ x).

  Definition tm_make_interp_branches (xs: list term) : TemplateMonad (list (branch term)) := 
    tmReturn (map make_interp_branch xs).

  Definition do_one_branch (x: packed) : TemplateMonad (branch term) :=
    match x with 
    | pack x' => 
      tmQuote x' >>= (liftM make_interp_branch)
    end.

  Definition tm_make_interp_branches_p (xs: list packed) : TemplateMonad (list (branch term)) := 
    mapM do_one_branch xs.

  Definition quote_dest_ind (t: Type) := 
    sorts_term <- tmQuote t ;;
    match sorts_term with 
    | tInd ind _ => tmReturn (sorts_term, ind)
    | _ => 
      tmMsg "sort input was not actually a inductive!" ;; 
      tmPrint sorts_term ;;
      tmFail "bad sort input"
    end.

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

  Definition n_to_str (n: nat) : string := 
    BinaryString.of_nat n.

  Definition mk_fun_ctor (name: ident) (indices: list term) : constructor_body := {| 
    cstr_name := name ++ "_f";
    cstr_args := [];
    cstr_indices := [];
    cstr_type := tApp (tRel 0) indices;
    cstr_arity := 0;
  |}.

  Definition funs_one_body (fun_args_term: term) (fun_ret_term: term)
  (names: list ident) (indices: list (list term)) (funs_type: term) : one_inductive_body := {|
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
    ind_ctors := map (fun '(name, idxs) => mk_fun_ctor name idxs) (List.combine names indices);
    ind_projs := [];
    ind_relevance := Relevant
  |}.

  Definition funs_body (funs_arg_term : term) (funs_ret_term: term) (names: list ident) (indices: list (list term)) (funs_type : term) : mutual_inductive_body := {| 
    ind_finite := Finite;
    ind_npars := 0;
    ind_params := [];
    ind_bodies := [
      funs_one_body funs_arg_term funs_ret_term names indices funs_type
    ];
    ind_universes := Monomorphic_ctx;
    ind_variance := None;
  |}.

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
    (* | tRel _ => [t] *)
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

  Fixpoint unquote_indices_helper (sorts: Type) (terms: list term) : TemplateMonad (list sorts) := 
    match terms with 
    | [] => tmReturn []
    | t :: ts => 
      x <- tmUnquoteTyped sorts t ;;
      x' <- unquote_indices_helper sorts ts ;;
      tmReturn (x :: x')
    end.

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

  Fixpoint unquote_indices (sorts: Type) (indices: list (list term)) : TemplateMonad (list (list sorts * sorts)) := 
    match indices with 
    | [] => tmReturn []
    | t :: ts => 
      x <- unquote_indices_helper sorts t ;;
      match get_last x with 
      | Some v => 
        r <- unquote_indices sorts ts ;;
        tmReturn (v :: r)
      | None => tmFail "empty indices??"
      end
    end.

  Fixpoint quote_indices (sorts: Type) (indices : list (list sorts * sorts)) : TemplateMonad (list (list term)) :=
    match indices with 
    | nil => tmReturn nil
    | (args, ret) :: indices' => 
      args_term <- tmQuote args ;;
      ret_term <- tmQuote ret ;;
      r <- quote_indices _ indices' ;;
      tmReturn ([args_term; ret_term] :: r)
    end.

  Definition add_funs_type (sorts: Type) (names: list ident) (indices : list (list sorts * sorts)) : TemplateMonad unit := 
    arg_term <- tmQuote (list sorts) ;;
    ret_term <- tmQuote sorts ;;
    funs_ty_term <- tmQuote (list sorts -> sorts -> Type) ;;
    indices' <- quote_indices sorts indices ;;
    tmMkInductive' (funs_body arg_term ret_term names indices' funs_ty_term).

  Definition get_ty_name (t: term) : TemplateMonad ident := 
    match t with 
    | tInd ind _ => tmReturn (snd ind.(inductive_mind))
    | tVar s => tmReturn s
    | _ => 
      tmMsg "can't get name from:" ;;
      tmPrint t ;;
      tmFail "get_ty_name"
    end.


  Definition make_names (xs: list term) : TemplateMonad (list ident) := 
    mapM get_ty_name xs.

  Definition uniq_term := uniq _ Core.eq_term.

  Definition sorts_constant_body (x: constant_body) : list term := 
    normalize_sort_term x.(cst_type).

  (* sadly this subst needs to normalize variables for the binder as it goes.
     The proper thing is probably to tweak subst so that it properly reasons about variable indices as it does the substitution.
  *)
  Definition get_ctor_type (t: term) (x: constructor_body) : list term :=
    normalize_sort_term (subst_terms [(tRel 0, t)] x.(cstr_type)).
  
  Definition get_ctor_name (x: constructor_body) : ident := x.(cstr_name).

  Definition sorts_mind_body (t: term) : TemplateMonad (list (ident * list term)) := 
    match t with 
    | tInd ind  _ => 
      x <- tmQuoteInductive ind.(inductive_mind) ;;
      match x.(ind_bodies) with 
      | [i] => 
        tmPrint "ctor types:" ;; 
        x <- tmEval all (map (fun c => c.(cstr_type)) i.(ind_ctors)) ;;
        tmPrint x ;;
        tmReturn ( map (fun c => (get_ctor_name c, get_ctor_type t c)) i.(ind_ctors))
      | _ => tmFail "mutually inductive inds are not currently supported"
      end
    | _ => tmFail "sorts_mind_body called with non-ind input"
    end.

  Definition gather_sorts (t: packed) : TemplateMonad (list (ident * list term)) := 
    match t with 
    | pack x => 
      t' <- tmQuote x ;;
      match t' with 
      | tInd _ _ => sorts_mind_body t'
      | tConst name _ => 
        y <- tmQuoteConstant name true ;;
        x <- tmEval all (sorts_constant_body y) ;;
        tmReturn [(snd name, x)]
      | _ => 
        tmMsg "unrecognized term" ;;
        tmPrint t' ;;
        tmFail "unrecognized term in gather sorts"
      end
    end.


  Fixpoint gather_sorts_all (xs: list packed) : TemplateMonad (list ( ident * list term)) := 
    match xs with 
    | nil => tmReturn nil
    | (x :: xs')%list => 
      t <- gather_sorts x ;;
      t' <- gather_sorts_all xs' ;;
      tmReturn (t ++ t')%list
    end.


  (* TODO: 
    1) add a new sort interpretation, unquoting sort_ty_terms to get the types
    2) add function symbols, using the new sort and the indices as constructor arguments
    
  *)


  Definition add_sorts_indices (indices: list (list term)) := 
    let sort_ty_terms := uniq_term (concat indices) in 
      sort_names <- make_names sort_ty_terms ;;
      sort_terms <- add_sorts sort_names ;;
      tmReturn (combine sort_ty_terms sort_terms).


  From MetaCoq.Translations Require Import translation_utils.


  Definition config_level : Universe.t := Universe.of_levels (inr (Level.Level "Config.17")).

  Definition extr_univ (t: term) : Universe.t := 
    match t with 
    | tSort u => u
    | _ => config_level
    end.

  Fixpoint rep_sorts_level (univ: Universe.t) (t: term) := 
    match t with 
    | tSort _ => tSort univ
    | tProd x t ts => 
      tProd x (rep_sorts_level univ t) (rep_sorts_level univ ts)
    | _ => t
    end.

  (* Generate sorts, sort interpretation, and function symbols for an 
     input list of either top-level function definitions, or top-level inductive definitions.
     For inductive definitions, treat the constructors of the inductive as function definitions.
     Generates syntax and semantics for the types of the input functions (but does not examine their bodies).
  *)

  Definition add_funs (typ_term: term) (funs: list packed) : TemplateMonad unit := 
    names_indices <- gather_sorts_all funs ;;
    let '(names, normal_indices) := List.split names_indices in 
    sorted_indices <- add_sorts_indices normal_indices ;; 
    (* tmPrint "lookup table for interp sorts:" ;;
    v <- tmEval all sorted_indices ;;
    tmPrint v;; *)
    srts <- tmLocate "sorts" ;;
    match srts with 
    | [] => tmFail "error making sorts"
    | srt :: _ =>
      srt <- tmUnquoteTyped Type (monomorph_globref_term srt) ;;
      add_interp_sorts (fst (split sorted_indices)) srt ;;
      arg_term <- tmQuote (list srt) ;;
      ret_term <- tmQuote srt ;;
      funs_ty_term <- tmQuote (list srt -> srt -> Type) ;;
      idx' <- unquote_indices srt (map (map (subst_terms sorted_indices)) normal_indices) ;;
      idx'' <- quote_indices srt idx' ;;
      foo <- tmEval all normal_indices ;;
      tmMkInductive' (funs_body arg_term ret_term names idx'' (rep_sorts_level (extr_univ typ_term) funs_ty_term) ) ;;
      tmMsg "added function symbol inductive fol_funs"
    end.


  (* code for autogenerating boolean term tests *)

  Definition mk_test_lambda (t: term) : term := 
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
        [tRel 0; t];
     tApp
       (tConst (MPfile ["Core"; "Reflection"; "MirrorSolve"]%list, "eq_term")
          nil)
       [tRel 0; t]]).

  Definition mk_test (name: ident) (t: packed) := 
    match t with 
    | pack x =>
      t' <- tmQuote2 x ;;
      let name' := ("is_" ++ name ++ "_t") in 
      tmMkDefinition name' (mk_test_lambda t') ;;
      tmMsg ("added definition for " ++ name')
    end.
    
  (* Add boolean term tests for a list of input definitions. 
    Names using the Coq name of the definition.  
    *)
  Definition add_test (x: packed) := 
    match x with 
    | pack x' => 
      t <- tmQuote x' ;;
      match t with 
      | tConst name _ => 
        mk_test (snd name) x
      | tConstruct ind idx _ => 
        inds <- tmQuoteInductive ind.(inductive_mind) ;;
        match nth_error inds.(ind_bodies) ind.(inductive_ind)  with 
        | Some ind' =>
          match nth_error ind'.(ind_ctors) idx with 
          | Some ctor => 
            mk_test ctor.(cstr_name) x
          | None => tmFail "incorrect index into ctors??"
          end
        | None => tmFail "incorrect index into inds??"
        end
      | _ => 
        tmPrint t ;;
        tmFail "unhandled term for getting name in add_test"
      end
    end.

  Definition add_tests (xs: list packed) :=
    mapM add_test xs.

End Config.

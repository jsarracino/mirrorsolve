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

Polymorphic Fixpoint sequence {A} (acts: list (TemplateMonad A)) : TemplateMonad (list A) := 
  match acts with 
  | [] => tmReturn []
  | a :: acts' => 
    x <- a ;;
    r <- sequence acts' ;;
    tmReturn (x :: r)
  end.

Polymorphic Definition mapM {A B} (f: A -> TemplateMonad B) (xs: list A) : TemplateMonad (list B) :=
  sequence (map f xs).

Polymorphic Definition fmap {A B} (f: A -> B) (t: TemplateMonad A) : TemplateMonad B := 
  t >>= (fun x => tmReturn (f x)).

Polymorphic Definition liftM {A B} (f: A -> B) : A -> TemplateMonad B := 
  fun a => tmReturn (f a).

Polymorphic Definition tmQuote2 {X} (x: X) := 
  tmQuote x >>= tmQuote.

Polymorphic Definition make_ind_ctor (ind: inductive) (u: Instance.t) (idx: nat) (x: constructor_body) : term := 
    tConstruct ind idx u.

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


Require Import MirrorSolve.FirstOrder.

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

  Definition add_sorts (names: list ident) : TemplateMonad (list term) := 
    tmMkInductive' (sorts_body names) ;;
    tmPrint "added inductive definition for sorts" ;;
    srts <- tmLocate "sorts" ;; 
    match srts with 
    | nil => tmFail "new sort not named sorts"
    | (IndRef i) :: _ => tmReturn (map_with_index (mk_sorts_ctor i []) names)
    | _ => tmFail "sorts is not an inductive!"
    end.

  MetaCoq Quote Definition t_bool := (bool).
  MetaCoq Quote Definition t_prop := (Prop).

  Definition make_interp_branch (r: term) : branch term :=  {|
    bcontext := [];
    bbody := if Core.eq_term r t_prop then t_bool else r
  |}.

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


  Definition mk_rel_ctor (name: ident) (indices: list term) : constructor_body := {| 
    cstr_name := name ++ "_r";
    cstr_args := [];
    cstr_indices := [];
    cstr_type := tApp (tRel 0) indices;
    cstr_arity := 0;
  |}.

  Definition funs_one_body (z_index: option term) (t_nil : term) (fun_args_term: term) (fun_ret_term: term)
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
    ind_ctors := 
      List.app 
        (map (fun '(name, idxs) => mk_fun_ctor name idxs) (List.combine names indices))
        (match z_index with | Some x => [z_const_ctor x t_nil] | _ => [] end );
    ind_projs := [];
    ind_relevance := Relevant
  |}.

  Definition funs_body (z_index : option term) (t_nil: term) (funs_arg_term : term) (funs_ret_term: term) (names: list ident) (indices: list (list term)) (funs_type : term) : mutual_inductive_body := {| 
    ind_finite := Finite;
    ind_npars := 0;
    ind_params := [];
    ind_bodies := [
      funs_one_body z_index t_nil funs_arg_term funs_ret_term names indices funs_type
    ];
    ind_universes := Monomorphic_ctx;
    ind_variance := None;
  |}.

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
    | tSort _ => 
      if Core.eq_term t t_prop then [t] else []
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

  Definition unquote_rel_indices (sorts: Type) (indices: list (list term)) : TemplateMonad (list (list sorts)) := 
    mapM (unquote_indices_helper sorts) indices.

  Fixpoint quote_fun_indices (sorts: Type) (indices : list (list sorts * sorts)) : TemplateMonad (list (list term)) :=
    match indices with 
    | nil => tmReturn nil
    | (args, ret) :: indices' => 
      args_term <- tmQuote args ;;
      ret_term <- tmQuote ret ;;
      r <- quote_fun_indices _ indices' ;;
      tmReturn ([args_term; ret_term] :: r)
    end.

  Fixpoint quote_rel_indices (sorts: Type) (indices : list (list sorts)) : TemplateMonad (list (list term)) :=
    match indices with 
    | nil => tmReturn nil
    | args :: indices' => 
      args_term <- tmQuote args ;;
      r <- quote_rel_indices _ indices' ;;
      tmReturn ([args_term] :: r)
    end.

  Definition add_funs_type (sorts: Type) (names: list ident) (indices : list (list sorts * sorts)) : TemplateMonad unit := 
    arg_term <- tmQuote (list sorts) ;;
    ret_term <- tmQuote sorts ;;
    funs_ty_term <- tmQuote (list sorts -> sorts -> Type) ;;
    nil_term <- tmQuote (@nil sorts) ;;
    indices' <- quote_fun_indices sorts indices ;;
    tmMkInductive' (funs_body None nil_term arg_term ret_term names indices' funs_ty_term).

  Definition get_ty_name (t: term) : TemplateMonad ident := 
    match t with 
    | tInd ind _ => tmReturn (snd ind.(inductive_mind))
    | tVar s => tmReturn s
    | tSort (Universe.lProp) => tmReturn "prop"
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

  Definition get_ctor_type (t: term) (x: constructor_body) : list term :=
    normalize_sort_term (subst_terms [(tRel 0, t)] x.(cstr_type)).
  
  Definition get_ctor_name (x: constructor_body) : ident := x.(cstr_name).

  Definition sorts_mind_body (t: term) : TemplateMonad (list (ident * list term)) := 
    match t with 
    | tInd ind  _ => 
      x <- tmQuoteInductive ind.(inductive_mind) ;;
      match x.(ind_bodies) with 
      | [i] => 
        (* tmPrint "ctor types:" ;;  *)
        x <- tmEval all (map (fun c => c.(cstr_type)) i.(ind_ctors)) ;;
        tmPrint x ;;
        tmReturn ( map (fun c => (get_ctor_name c, get_ctor_type t c)) i.(ind_ctors))
      | _ => tmFail "mutually inductive inds are not currently supported"
      end
    | _ => tmFail "sorts_mind_body called with non-ind input"
    end.

  Definition gather_sorts (t: packed) : TemplateMonad (list (ident * list term)) := 
    t' <- tmQuotePacked t ;;
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
    end.


  Fixpoint gather_sorts_all (xs: list packed) : TemplateMonad (list ( ident * list term)) := 
    match xs with 
    | nil => tmReturn nil
    | (x :: xs')%list => 
      t <- gather_sorts x ;;
      t' <- gather_sorts_all xs' ;;
      tmReturn (t ++ t')%list
    end.

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
    | tInd ind u => get_ind_ctors ind u 
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
    mp_srts : list (term * term) ;
    mp_funs : list (term * term) ; 
    mp_rels : list (term * term) ;
  }.

  Definition all_symbs (t: translation_table) := List.app t.(mp_funs) t.(mp_rels).

  MetaCoq Quote Definition t_z := (BinInt.Z).

  Definition is_z_srt (t: term) := Core.eq_term t t_z.

  Fixpoint gather_z_const (srts: list (term * term)) : option term := 
    match srts with 
    | [] => None
    | (typ, idx) :: xs => 
      if is_z_srt typ then Some idx else gather_z_const xs 
    end.



  Definition add_funs (typ_term: term) (funs: list packed) (rels: list packed) : TemplateMonad translation_table := 
    names_indices <- gather_sorts_all (List.app funs rels) ;;
    names_funs_rels <- fmap split_sum_list (mapM split_fun_rel names_indices) ;; 

    let '(names_funs, fun_indices) := List.split names_funs_rels.1 in 
    let '(names_rels, rel_indices) := List.split names_funs_rels.2 in 

    sorted_indices <- add_sorts_indices (fun_indices ++ rel_indices ++ [[t_prop]]) ;; 
    let z_const_opt := gather_z_const sorted_indices in 

    srts <- tmLocate "sorts" ;;
    match srts with 
    | [] => tmFail "error making sorts"
    | srt :: _ =>
      srt <- tmUnquoteTyped Type (monomorph_globref_term srt) ;;
      add_interp_sorts (fst (split sorted_indices)) srt ;;

      arg_term <- tmQuote (list srt) ;;
      ret_term <- tmQuote srt ;;
      funs_ty_term <- tmQuote (list srt -> srt -> Type) ;;
      rels_ty_term <- tmQuote (list srt -> Type) ;;
      nil_term <- tmQuote (@nil srt) ;;

      idx' <- unquote_fun_indices srt (map (map (subst_terms sorted_indices)) fun_indices) ;;
      idx'' <- quote_fun_indices srt idx' ;;
      tmMkInductive' (funs_body z_const_opt nil_term arg_term ret_term names_funs idx'' (rep_sorts_level (extr_univ typ_term) funs_ty_term) ) ;;
      tmMsg "added function symbol inductive fol_funs" ;;

      idx' <- unquote_rel_indices srt (map (map (subst_terms sorted_indices)) rel_indices) ;;
      idx'' <- quote_rel_indices srt idx' ;;
      tmMkInductive' (rel_body arg_term names_rels idx'' (rep_sorts_level (extr_univ typ_term) rels_ty_term) ) ;;
      tmMsg "added relation symbol inductive fol_rels" ;;

      funs' <- tmLocate "fol_funs" ;;
      rels' <- tmLocate "fol_rels" ;;
      match funs', rels' with 
      | IndRef ind_f :: _, IndRef ind_r :: _ => 
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
          |}

        | _ , _ => tmFail "unexpected size of funs/rels  inductive"
        end
      | _, _ => tmFail "error making funs"
      end
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

  Definition mk_test_plain (name: ident) (t: term) := 
    t' <- tmQuote t ;;
    let name' := ("is_" ++ name ++ "_t") in 
    tmMkDefinition name' (mk_test_lambda t').

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
    typed_tms <- tmLocate id ;;
    match typed_tms with
    | nil =>
      tmFail "Failed to look up signature"
    | typed_tm :: _ =>
      tmUnquoteTyped A (monomorph_globref_term typed_tm) >>= tmReturn
    end
  .

  Definition gen_sig'
    (sort_type : term)
    (fun_type: term)
    (rel_type: term)
  :
    TemplateMonad ident
  :=
    builder <- tmQuote Build_signature ;;
    builder' <- tmEval all builder ;;
    tmMsg "builder:" ;;
    tmPrint builder' ;;
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
  Definition pack_fs (s: FirstOrder.signature) (m: FirstOrder.model s) := {args_r & s.(sig_funs) args_r.1 args_r.2}.
  Definition pack_rs (s: FirstOrder.signature) (m: FirstOrder.model s) := {args & s.(sig_rels) args}.


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
    test <- tmUnquoteTyped (term -> bool) (mk_test_lambda x) ;;
    tac <- coerce_tac_syn_f symb ;;
    tmReturn (test, tac).
  Definition build_rel_match {s: FirstOrder.signature} {m: FirstOrder.model s} (orig: term) (symb: term) : TemplateMonad ((term -> bool) * Tactics.tac_syn s m) :=
    x <- tmQuote orig ;;
    test <- tmUnquoteTyped (term -> bool) (mk_test_lambda x) ;;
    tac <- coerce_tac_syn_r symb ;;
    tmReturn (test, tac).

  Definition build_sort_match {s: FirstOrder.signature} {m: FirstOrder.model s} (orig: term) (symb: term) : TemplateMonad ((term -> bool) * s.(sig_sorts)) := 
    x <- tmQuote orig ;;
    test <- tmUnquoteTyped (term -> bool) (mk_test_lambda x) ;;
    srt <- tmUnquoteTyped s.(sig_sorts) symb ;;
    tmReturn (test, srt).

  Definition add_symb_matches (s: FirstOrder.signature) (m: FirstOrder.model s) (t: translation_table) : TemplateMonad unit := 
    fun_matches <- mapM (fun '(orig_f, sym_f) => @build_fun_match s m orig_f sym_f) t.(mp_funs) ;;
    rel_matches <- mapM (fun '(orig_r, sym_r) => @build_rel_match s m orig_r sym_r) t.(mp_rels) ;;
    matches_term <- tmQuote (List.app fun_matches rel_matches) ;;
    tmMkDefinition "match_tacs" matches_term.

  Definition add_sort_matches (s: FirstOrder.signature) (m: FirstOrder.model s) (t: translation_table) : TemplateMonad unit := 
    sort_matches <- mapM (fun '(orig, sym) => @build_sort_match s m orig sym) t.(mp_srts) ;;
    matches_term <- tmQuote sort_matches ;;
    tmMkDefinition "match_sorts" matches_term.

  Definition add_matches (s: FirstOrder.signature) (m: FirstOrder.model s) (t: translation_table) : TemplateMonad unit := 
    add_symb_matches s m t ;;
    add_sort_matches s m t.

End Config.

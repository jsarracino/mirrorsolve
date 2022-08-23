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

Fixpoint tm_make_interp_branches (xs: list Type) (ys: list Set) : TemplateMonad (list (branch term)) := 
  match xs with 
  | nil => (fix rec ys := 
      match ys with 
      | nil => tmReturn nil
      | y :: ys' => 
        t <- tmQuote y ;;
        r <- rec ys' ;;
        tmReturn (make_interp_branch t :: r)
      end
    ) ys
  | x :: xs' => 
    t <- tmQuote x ;;
    r <- tm_make_interp_branches xs' ys ;;
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


Definition add_interp_sorts (tys: list Type) (sets: list Set) (sorts: Type) := 
  '(sort_term, ind) <- quote_dest_ind sorts ;;
  brs <- tm_make_interp_branches tys sets ;;
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

Definition add_funs_type (sorts: Type) (indices : list (list term)) := 
  arg_term <- tmQuote (list sorts) ;;
  ret_term <- tmQuote sorts ;;
  funs_ty_term <- tmQuote (list sorts -> sorts -> Type) ;;
  tmMkInductive' (funs_body arg_term ret_term indices funs_ty_term).
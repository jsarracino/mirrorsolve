Require Import MetaCoq.Template.All.
Require Import Coq.Lists.List.
Import String.

Import MCMonadNotation.
Import ListNotations.
Open Scope bs.

Definition tmDebug {A: Type} (thing: A) : TemplateMonad unit :=
  tmEval all thing >>= tmPrint
.

Definition print_body {A: Type} (f: A) :=
  func_quoted <- tmQuote f ;;
  match func_quoted with
  | tConst kername _ =>
    tmQuoteConstant kername true >>= tmPrint
  | _ =>
    tmFail "Failed to look up body"
  end
.

Definition binder_anon :=
  {| binder_name := nAnon; binder_relevance := Relevant |}
.

Definition subst_recursive_args (rec: term) (args: context) :=
  map (fun arg => subst1 arg.(decl_type) 0 rec) args.

Fixpoint inspect_ctor_args
  (ind_term: term)
  (index: nat)
:=
  match ind_term with
  | tInd ind _ =>
    inductive_definition <- tmQuoteInductive ind.(inductive_mind) ;;
    match inductive_definition.(ind_bodies) with
    | first_body :: nil =>
      match nth_error first_body.(ind_ctors) index with
      | Some inductive_ctor =>
        tmReturn (List.length inductive_ctor.(cstr_args), nil)
      | None =>
        tmFail "Inductive constructor out of range"
      end
    | _ =>
      tmFail "Inductive has more than one body."
    end
  | tApp ind_term args =>
    mlet '(arg_count, type_args) <- inspect_ctor_args ind_term index ;;
    tmReturn (arg_count, args ++ type_args)%list
  | _ =>
    tmDebug ind_term ;;
    tmFail "Term is not an inductive."
  end
.

Fixpoint wrap_type (count: nat) (body: term) :=
  match count with
  | 0 => body
  | S count =>
    tProd binder_anon hole (wrap_type count body)
  end
.

Fixpoint wrap_body (count: nat) (body: term) :=
  match count with
  | 0 => body
  | S count =>
    tLambda binder_anon hole (wrap_body count body)
  end
.

Fixpoint dummy_args (count: nat) (offset: nat) :=
  match count with
  | 0 => nil
  | S count => List.app (dummy_args count (S offset)) [tRel offset]
  end
.

MetaCoq Quote Definition eq_quoted := @eq.
MetaCoq Quote Definition eq_refl_quoted := @eq_refl.

MetaCoq Quote Definition iff_quoted := @iff.
MetaCoq Quote Definition iff_refl_quoted := @iff_refl.

(* Custom version of MetaCoq's subst function. Theirs assumes that bound terms
   within the arguments will need to be shifted within the produced term, but
   in our case we do not want this to happen.

   Bear in mind that this may be unsound in general because of dependent
   types --- may the CIC gods have mercy on our souls. *)
Fixpoint subst_nolift (s : list term) (k : nat) (u : term) : term :=
  match u with
  | tRel n =>
      if PeanoNat.Nat.leb k n
      then
       match nth_error s (n - k) with
       | Some b => b
       | None => tRel (n - #|s|)
       end
      else tRel n
  | tEvar ev args => tEvar ev (map (subst s k) args)
  | tCast c kind ty => tCast (subst s k c) kind (subst s k ty)
  | tProd na A B => tProd na (subst s k A) (subst s (S k) B)
  | tLambda na T M => tLambda na (subst s k T) (subst s (S k) M)
  | tLetIn na b ty b' =>
      tLetIn na (subst s k b) (subst s k ty) (subst s (S k) b')
  | tApp u0 v => mkApps (subst s k u0) (map (subst s k) v)
  | tCase ind p c brs =>
      let k' := #|pcontext p| + k in
      let p' := map_predicate id (subst s k) (subst s k') p in
      let brs' := map_branches_k (subst s) k brs in
      tCase ind p' (subst s k c) brs'
  | tProj p c => tProj p (subst s k c)
  | tFix mfix idx =>
      let k' := #|mfix| + k in
      let mfix' := map (map_def (subst s k) (subst s k')) mfix in
      tFix mfix' idx
  | tCoFix mfix idx =>
      let k' := #|mfix| + k in
      let mfix' := map (map_def (subst s k) (subst s k')) mfix in
      tCoFix mfix' idx
  | _ => u
  end.

Definition infer_equation
  (arg_type_quoted: term)
  (ret_type_quoted: term)
  (func_quoted: term)
  (info: case_info)
  (body: term)
  (depth: nat)
  (offset: nat)
  (index: nat)
:=
  mlet (arg_count, inst_args) <- inspect_ctor_args arg_type_quoted index ;;
  match func_quoted with
  | tConst (_, func_name) _ =>
    let construct := tApp (tConstruct info.(ci_ind) index [])
                          (inst_args ++ dummy_args arg_count 0)%list in
    let args_pre := dummy_args (depth-1-offset) (offset+arg_count) in
    let args_post := dummy_args offset arg_count in
    let args := (args_pre ++ [construct] ++ args_post)%list in
    let claim_lhs := tApp func_quoted args in
    let claim_rhs := subst_nolift [construct] (offset+arg_count) body in
    let (claim_prefix, proof_prefix) :=
      match ret_type_quoted with
      | tSort Universe.lProp =>
        (iff_quoted, iff_refl_quoted)
      | _ =>
        (tApp eq_quoted [hole], tApp eq_refl_quoted [hole])
      end in
    let claim_eq := tApp claim_prefix [claim_lhs; claim_rhs] in
    let claim_quoted := wrap_type (arg_count+depth-1) claim_eq in
    claim <- tmUnquoteTyped Type claim_quoted ;;
    let proof_quoted :=
      wrap_body (arg_count+depth-1) (tApp proof_prefix [claim_rhs]) in
    proof <- tmUnquoteTyped claim proof_quoted ;;
    let eqn_base := func_name ++ "_equation_" ++ string_of_nat (index+1) in
    eqn_name <- tmFreshName eqn_base ;;
    tmDefinitionRed eqn_name (Some (unfold (Common_kn "my_projT1"))) proof ;;
    tmReturn tt
  | _ => tmFail "Symbol is not a constant."
  end
.

Fixpoint infer_equations_walk_cases
  (arg_type_quoted: term)
  (ret_type_quoted: term)
  (func_quoted: term)
  (info: case_info)
  (bodies: list (branch term))
  (depth: nat)
  (offset: nat)
  (index: nat)
:=
  match bodies with
  | nil => tmReturn 0
  | body :: bodies =>
    infer_equation arg_type_quoted ret_type_quoted func_quoted info body.(bbody) depth offset index ;;
    infer_equations_walk_cases arg_type_quoted ret_type_quoted func_quoted info bodies depth offset (S index)
  end
.

Fixpoint infer_equations_inner
  (body: term)
  (top_quoted: term)
  (context: list term)
:=
  match body with
  | tLambda _ arg_type_quoted body =>
    infer_equations_inner body top_quoted (arg_type_quoted :: context)
  | tCase info pred (tRel offset) bodies =>
    match nth_error context offset with
    | Some arg_type_quoted =>
      infer_equations_walk_cases arg_type_quoted pred.(preturn) top_quoted info bodies (List.length context) offset 0
    | None =>
      tmFail "Term contains match on something that is not an argument."
    end
  | _ =>
    tmFail "Symbol body is not a function with a match inside."
  end
.

Definition infer_equations_handle_fixpoint
  (body: term)
  (func_quoted: term)
:=
  match body with
  | tFix (first_fixpoint :: nil) 0 =>
    let body := subst10 func_quoted first_fixpoint.(dbody) in
    infer_equations_inner body func_quoted nil
  | _ =>
    infer_equations_inner body func_quoted nil
  end
.

Definition infer_equations {A: Type} (func: A) :=
  func_quoted <- tmQuote func ;;
  match func_quoted with
  | tConst func_path _ =>
    def <- tmQuoteConstant func_path true ;;
    match def.(cst_body) with
    | Some body =>
      infer_equations_handle_fixpoint body func_quoted
    | None =>
      tmFail "Function does not seem to have a body."
    end
  | _ => tmFail "Symbol is not a constant."
  end
.

Section Tests.
  Definition decr (n: nat) : nat :=
    match n with
    | 0 => 0
    | S n => n
    end
  .
  MetaCoq Run (infer_equations decr).
  Check decr_equation_1.
  Check decr_equation_2.

  Definition decr_strange (n: nat) : nat :=
    match n with
    | 0 => 0
    | S m => n
    end
  .

  MetaCoq Run (infer_equations decr_strange).
  Check decr_strange_equation_1.
  Check decr_strange_equation_2.

  Definition decr_multi_arg (n m: nat) :=
    match n with
    | 0 => m
    | S n => n
    end.

  MetaCoq Run (infer_equations decr_multi_arg).
  Check decr_multi_arg_equation_1.
  Check decr_multi_arg_equation_2.

  Fixpoint decr_rec (n: nat) : nat :=
    match n with
    | 0 => 0
    | S n => decr_rec n
    end
  .

  MetaCoq Run (infer_equations decr_rec).
  Check decr_rec_equation_1.
  Check decr_rec_equation_2.

  Fixpoint decr_rec_multi_arg (n m: nat) : nat :=
    match n with
    | 0 => m
    | S n => decr_rec_multi_arg n m
    end
  .

  MetaCoq Run (infer_equations decr_rec_multi_arg).
  Check decr_rec_multi_arg_equation_1.
  Check decr_rec_multi_arg_equation_2.

  MetaCoq Run (infer_equations Nat.add).
  Check add_equation_1.
  Check add_equation_2.

  MetaCoq Run (infer_equations Nat.mul).
  Check mul_equation_1.
  Check mul_equation_2.

  Definition app_nat := Eval compute in (@List.app nat).

  MetaCoq Run (infer_equations app_nat).
  Check app_nat_equation_1.
  Check app_nat_equation_2.

  Fixpoint NoDup_nat (xs: list nat) :=
    match xs with
    | [] => True
    | x' :: xs' =>
      ~ In x' xs' /\ NoDup_nat xs'
    end.
  MetaCoq Run (infer_equations NoDup_nat).
  Check NoDup_nat_equation_1.
  Check NoDup_nat_equation_2.
End Tests.

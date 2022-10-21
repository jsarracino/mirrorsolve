Require Import MetaCoq.Template.All.
Require Import Coq.Lists.List.
Import String.

Import MCMonadNotation.
Import ListNotations.
Open Scope bs.

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

Definition constructor_argument_count
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
        tmReturn (List.length inductive_ctor.(cstr_args))
      | None =>
        tmFail "Inductive constructor out of range"
      end
    | _ =>
      tmFail "Inductive has more than one body."
    end
  | _ =>
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
    tLambda binder_anon hole (wrap_type count body)
  end
.

Fixpoint dummy_args (count: nat) (offset: nat) :=
  match count with
  | 0 => nil
  | S count => tRel offset :: dummy_args count (S offset)
  end
.

MetaCoq Quote Definition eq_quoted := @eq.
MetaCoq Quote Definition eq_refl_quoted := @eq_refl.

Definition infer_equation
  (arg_type_quoted: term)
  (func_quoted: term)
  (info: case_info)
  (body: term)
  (index: nat)
:=
  arg_count <- constructor_argument_count arg_type_quoted index ;;
  match func_quoted with
  | tConst (_, func_name) _ =>
    let claim_lhs := tApp func_quoted
                          [tApp (tConstruct info.(ci_ind) index [])
                                (dummy_args arg_count 0)] in
    let claim_quoted :=
      wrap_type arg_count (tApp eq_quoted [hole; claim_lhs; body]) in
    claim <- tmUnquoteTyped Type claim_quoted ;;
    let proof_quoted :=
      wrap_body arg_count (tApp eq_refl_quoted [hole; body]) in
    proof <- tmUnquoteTyped claim proof_quoted ;;
    let eqn_base := func_name ++ "_equation_" ++ string_of_nat (index+1) in
    eqn_name <- tmFreshName eqn_base ;;
    tmDefinitionRed eqn_name (Some (unfold (Common_kn "my_projT1"))) proof ;;
    tmReturn tt
  | _ => tmFail "Symbol is not a constant."
  end
.

Fixpoint infer_equations_inner
  (arg_type_quoted: term)
  (func_quoted: term)
  (info: case_info)
  (bodies: list (branch term))
  (index: nat)
:=
  match bodies with
  | nil => tmReturn 0
  | body :: bodies =>
    infer_equation arg_type_quoted func_quoted info body.(bbody) index ;;
    infer_equations_inner arg_type_quoted func_quoted info bodies (S index)
  end
.

Definition infer_equations {A: Type} (func: A) :=
  func_quoted <- tmQuote func ;;
  match func_quoted with
  | tConst func_path _ =>
    def <- tmQuoteConstant func_path true ;;
    match cst_body def with
    | Some (tLambda _ arg_type_quoted (tCase info _ (tRel 0) bodies)) =>
      infer_equations_inner arg_type_quoted func_quoted info bodies 0
    | Some (tFix (first_fixpoint :: nil) 0) =>
      match subst1 func_quoted 0 first_fixpoint.(dbody) with
      | tLambda _ arg_type_quoted (tCase info _ (tRel 0) bodies) =>
        infer_equations_inner arg_type_quoted func_quoted info bodies 0
      | _ => tmFail "foo"
      end
    | _ => tmFail "Symbol body is not a function with a match inside."
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

  Fixpoint decr_rec (n: nat) : nat :=
    match n with
    | 0 => 0
    | S n => decr_rec n
    end
  .

  MetaCoq Run (infer_equations decr_rec).
  Check decr_rec_equation_1.
  Check decr_rec_equation_2.
End Tests.

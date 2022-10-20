Require Import MetaCoq.Template.All.
Require Import Coq.Lists.List.
Import String.

Import MCMonadNotation.
Import ListNotations.
Open Scope bs.

Definition decr (n: nat) : nat :=
  match n with
  | 0 => 0
  | S n => n
  end
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

MetaCoq Run (print_body decr).

Definition binder_anon :=
  {| binder_name := nAnon; binder_relevance := Relevant |}
.

Definition subst_recursive_args (rec: term) (args: context) :=
  map (fun arg => subst1 arg.(decl_type) 0 rec) args.

Definition lookup_constructor_arguments
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
        tmReturn (subst_recursive_args ind_term inductive_ctor.(cstr_args))
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

Fixpoint wrap_type (args: list term) (body: term) :=
  match args with
  | nil => body
  | arg :: args =>
    tProd binder_anon arg (wrap_type args body)
  end
.

Fixpoint wrap_body (args: list term) (body: term) :=
  match args with
  | nil => body
  | arg :: args =>
    tLambda binder_anon arg (wrap_type args body)
  end
.

Fixpoint dummy_args (count: nat) (offset: nat) :=
  match count with
  | 0 => nil
  | S count => tRel offset :: dummy_args count (S offset)
  end
.

Definition infer_equation
  (return_type_quoted: term)
  (arg_type_quoted: term)
  (func_quoted: term)
  (mtype: case_info)
  (body: branch term)
  (index: nat)
:=
  return_type <- tmUnquoteTyped Type return_type_quoted ;;
  eq_refl_quoted <- tmQuote (@eq_refl return_type) ;;
  eq_quoted <- tmQuote (@eq) ;;
  args <- lookup_constructor_arguments arg_type_quoted index ;;
  match func_quoted with
  | tConst (_, func_name) _ =>
    let claim_quoted :=
      wrap_type
        args
        (tApp eq_quoted
              [return_type_quoted;
               tApp func_quoted
                    [tApp (tConstruct mtype.(ci_ind) index [])
                          (dummy_args (List.length args) 0)];
               body.(bbody)]) in
    claim <- tmUnquoteTyped Type claim_quoted ;;
    let proof_quoted :=
      wrap_body args (tApp eq_refl_quoted [body.(bbody)]) in
    proof <- tmUnquoteTyped claim proof_quoted ;;
    let eqn_base := func_name ++ "_equation_" ++ string_of_nat (index+1) in
    eqn_name <- tmFreshName eqn_base ;;
    tmDefinitionRed eqn_name
                    (Some (unfold (Common_kn "my_projT1")))
                    proof ;;
    tmReturn tt
  | _ => tmFail "Symbol is not a constant."
  end
.

Fixpoint infer_equations_inner
  (return_type_quoted: term)
  (arg_type_quoted: term)
  (func_quoted: term)
  (info: case_info)
  (bodies: list (branch term))
  (index: nat)
:=
  match bodies with
  | nil => tmReturn 0
  | body :: bodies =>
    infer_equation return_type_quoted
                   arg_type_quoted
                   func_quoted
                   info
                   body
                   index ;;
    infer_equations_inner
                   return_type_quoted
                   arg_type_quoted
                   func_quoted
                   info
                   bodies
                   (S index)
  end
.

Definition infer_equations {A: Type} (func: A) :=
  func_quoted <- tmQuote func ;;
  match func_quoted with
  | tConst func_path _ =>
    def <- tmQuoteConstant func_path true ;;
    return_type_quoted <-
      match def.(cst_type) with
      | tProd _ _ t =>
        tmReturn t
      | _ => tmFail "Symbol type is not a function type."
      end ;;
    match cst_body def with
    | Some (tLambda _ arg_type_quoted (tCase info _ (tRel 0) bodies)) =>
      infer_equations_inner return_type_quoted
                            arg_type_quoted
                            func_quoted
                            info
                            bodies
                            0
    | _ => tmFail "Symbol body is not a function with a match inside."
    end
  | _ => tmFail "Symbol is not a constant."
  end
.

MetaCoq Run (infer_equations decr).

Check decr_equation_1.
Check decr_equation_2.

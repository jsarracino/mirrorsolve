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

Definition infer_equation {A: Type} (func: A) :=
  func_quoted <- tmQuote func ;;
  match func_quoted with
  | tConst (modpath, func_name) _ =>
    def <- tmQuoteConstant (modpath, func_name) true ;;
    return_type <- match def.(cst_type) with
                   | tProd _ _ t =>
                     tmUnquoteTyped Type t
                   | _ => tmFail "Symbol type is not a function type."
                   end ;;
    return_type_quoted <- tmQuote return_type ;;
    proof_body <- tmQuote (@eq_refl return_type) ;;
    eq_quoted <- tmQuote (@eq) ;;
    match cst_body def with
    | Some (tLambda _ _ (tCase mtype _ (tRel 0) body)) =>
      match body with
      | first_body :: _ =>
        let claimed_equivalence :=
          tApp
            eq_quoted
            [return_type_quoted;
             tApp func_quoted [tConstruct mtype.(ci_ind) 0 []];
             first_body.(bbody)]
          in
        claim <- tmUnquoteTyped Type claimed_equivalence ;;
        proof <- tmUnquoteTyped claim (tApp proof_body [first_body.(bbody)]) ;;
        tmDefinitionRed (func_name ++ "_equation_1")
                        (Some (unfold (Common_kn "my_projT1")))
                        proof ;;
        tmReturn tt
      | _ => tmFail "Match does not contain at least one case."
      end
    | _ => tmFail "Symbol body is not a function with a match inside."
    end
  | _ => tmFail "Symbol is not a constant."
  end
.

MetaCoq Run (infer_equation decr).
Check decr_equation_1.

Require Import MirrorSolve.FirstOrder.

Require Import MirrorSolve.BV.
Require Import MirrorSolve.SMT.
Require Import MirrorSolve.UF.

Require Import MirrorSolve.FOList.

Require Import MirrorSolve.HLists.

Import HListNotations.

Require Import Coq.Strings.String.

Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.

Require Import Coq.ZArith.BinInt.
Require Import MirrorSolve.Automation.Equations.

(* In this demo we implement lists and some functions + relations over lists,
  and then and prove some properties about the functions and relations.
  1) my_rev, which is a naive quadratic list reverse (it uses append at each step, which is linear, on each element of the input)
  2) tail_rev, which is a classic tail-optimized linear list reverse.

  We prove that forall xs, my_rev xs = tail_rev xs using mirrorsolve's proof automation

  To demo the rest of mirrorsolve, we also define a length function, and a custom predicate, and prove properties about them with reverse.
*)

Declare ML Module "mirrorsolve.plugin".

Section ListFuncs.
  Variable (A: Type).
  Unset Universe Polymorphism.

  
  Inductive List (A: Type) := 
  | Nil 
  | Cons : A -> List A -> List A.

  Arguments Nil {A}.
  Arguments Cons {A}.

  Infix "::" := Cons.
  Notation "[]" := Nil.

  (* We will make use of a hint database to reflect recursive coq functions into SMT logic.
     For now, don't worry about it, but it's handy to use Equations for recursion to make use of the generated equations.
   *)

  Fixpoint app (l: List A) (r: List A) : List A := 
    match l with 
    | [] => r
    | (x :: l') => x :: app l' r
    end.

  (* MetaCoq Run (infer_equations app). *)

  (* Check app_equation_1.  *)
  (* forall x_0b0 : list A, app [] x_0b0 = x_0b0 *)
  (* Check app_equation_2.  *)
  (* 
    forall (x_0b10 : List A) (x_0b1 : A) (x_0b0 : List A),
      app (x_0b1 :: x_0b0) x_0b10 = x_0b1 :: app x_0b0 x_0b10 
    *)

  (* A list reverse function *)
  Fixpoint rev (xs: List A) : List A := 
    match xs with 
    | [] => []
    | x :: l' => app (rev l') (x :: [])
    end.

  (* MetaCoq Run (infer_equations rev). *)

  (* You can also use equations for functions! *)
  (* A tail recursive reverse function *)
  Equations tail_rev (xs: List A) (acc: List A) : List A := {
    tail_rev [] acc := acc;
    tail_rev (x :: xs') acc := tail_rev xs' (x :: acc);
  }.

  (* List membership as a fixpoint *)
  Fixpoint In (x: A) (l: List A) : Prop := 
    match l with 
    | [] => False
    | (x' :: l') => x = x' \/ In x l'
    end.

  (* Similar equations as before, but with <-> instead of =. *)
  (* MetaCoq Run (infer_equations In). *)
  

  (* List length using Z
  *)
  Equations len (xs: List A) : Z := {
    len [] := 0;
    len (_ :: xs) := len xs + 1;
  }.

  (* 
    An inductive list predicate, that a list doesn't contain any duplicates.
    Notice that we reuse the In membership predicate.
  *)

  Inductive NoDup : List A -> Prop :=
  | NoDup_nil : NoDup []
  | NoDup_cons : forall x l, 
    ~ In x l -> 
    NoDup l -> 
    NoDup (x::l).

  (* For this one we will need to reflect the behavior of NoDup on lists using iff equations.
   *)

  Lemma NoDup_equation_1 : 
    NoDup [] <-> True.
  Proof.
    intuition eauto || econstructor.
  Qed.

  Lemma NoDup_equation_2 : 
    forall x l, 
      NoDup (x :: l) <-> (
      ~ In x l  /\  NoDup l 
    ).
  Proof.
    intuition eauto.
    - inversion H; subst.
      contradiction.
    - inversion H; subst.
      trivial.
    - econstructor; eauto.
  Qed.

  (* Next we set up a first-order logic! *)

  

  From MetaCoq.Template Require Import All Loader.
  Import MCMonadNotation.
  Require Import MirrorSolve.Config.
  Open Scope bs.

  (* MirrorSolve's automation needs this later. *)
  Universe foo.
  MetaCoq Quote Definition typ_term := Type@{foo}.

  (* A large portion of MirrorSolve's automation is in the TemplateMonad,
     so we need to give a Coq type to a heterogeneous list of Coq values 
     (e.g. rev, app, List A). A lightweight way to do this is to pack the values with their type
     using an existential type, e.g. Definition packed := { T & T}.
  *)
  Notation pack x := (existT _ _ x).

  (* Here we define the inductive types and uninterpreted functions that MirrorSolve should reflect. 
     Under the hood, MirrorSolve infers what types are used, as well as how to reflect them.
    *)
  Definition fun_syms : List.list packed := [
      pack ListFuncs.rev
    ; pack ListFuncs.app
    ; pack (ListFuncs.List A)
    ; pack ListFuncs.tail_rev
    ; pack ListFuncs.len
    ; pack Z.add (* The body of len uses Z arithmetic, so we need to bring in Z.add as well. *)
  ].

  (* We distinguish between functions (which return values) and relations (which live in Coq's Prop).
     Here, we pass a list of Coq relations; each of these will also be reflected to an uninterpreted function.
  *)
  Definition rel_syms : List.list packed := [ 
      pack ListFuncs.In 
    ; pack ListFuncs.NoDup
  ].

  (* The final peice of configuration is to override some Coq functions with an SMT primitive.
     After all, we don't want to model *everything* with uninterpreted functions; for example,
     some Coq arithmetic functions (e.g. +, -, *, <, etc) should be modelled using corresponding SMT arithmetic primitives.

     In this case the only arithmetic function is addition, so we only need one primitive symbol.
     We record this in a list of arithmetic functions and their corresponding string symbol in SMT.
  *)
  Definition prim_syms : List.list (packed * String.string) := [
    (pack Z.add, "+"%string)
  ].

  (* The rest of the automation is copy-paste and should not change between developments. *)
  (* BEGIN BOILERPLATE *)

  MetaCoq Run (
    xs <- add_funs typ_term fun_syms rel_syms ;;
    xs' <- tmQuote xs ;;
    tmMkDefinition "trans_tbl" xs'
  ).
  MetaCoq Run (
    gen_sig typ_term sorts fol_funs fol_rels 
  ).
  MetaCoq Run (
    gen_interp_funs sorts interp_sorts fol_funs trans_tbl
  ).
  MetaCoq Run (
    gen_interp_rels sorts interp_sorts fol_rels trans_tbl
  ).
  Definition fm_model := Build_model sig interp_sorts interp_funs interp_rels.
  MetaCoq Run (
    match Utils.find _ _ smt_fun_base_beq IntLit (Utils.flip trans_tbl.(mp_consts)) with 
    | Some v => add_const_wf_instance sig fm_model v IntLit 
    | None => tmReturn tt
    end
  ).
  MetaCoq Run (
    match Utils.find _ _ smt_fun_base_beq BoolLit (Utils.flip trans_tbl.(mp_consts)) with 
    | Some v => add_const_wf_instance sig fm_model v BoolLit 
    | None => tmReturn tt
    end
  ).
  MetaCoq Run (
    add_matches sig fm_model trans_tbl
  ).
  MetaCoq Run (
    ctx <- build_printing_ctx sig sort_Prop trans_tbl prim_syms;; 
    ctx' <- tmEval all ctx ;;
    rhs <- tmQuote ctx' ;; 
    tmMkDefinition "fol_theory" rhs
  ).

  Require Import MirrorSolve.Reflection.Tactics.

  Transparent denote_tm.
  Require Import MirrorSolve.Axioms.

  (* We make use of the verification trick of negating the goal and checking for unsat. 
    The check_unsat_neg tactic behaves like idtac if the negated goal is unsat and otherwise fails.
    *)
  Ltac check_goal_unsat := 
    match goal with 
    | |- ?G => check_unsat_neg_func fol_theory G; eapply UnsoundAxioms.interp_true
    end.

  (* Finally we will set up a hint database for goals,
     as well as a runner script for adding the hint database, 
     reflecting the goal, 
     and calling the SMT solver.
     *)

  Ltac prep_proof := 
    hints_foreach (fun x => pose proof x) "list_eqns";
    Utils.revert_all;
    unfold "<->" in *.

  
  Scheme Equality for sorts.

  (* A wrapper around MirrorSolve's reflection tactic. *)
  Ltac quote_reflect_list := quote_reflect sig fm_model sorts_eq_dec match_tacs match_sorts.

  (* The overall proof script then: *)
  Ltac mirrorsolve :=
    prep_proof; (* 1) adds the list_eqns database to the proof goal as hypotheses, *)
    quote_reflect_list; (* 2) soundly reflects the goal to a structured first-order logic AST, *)
    check_goal_unsat. (* 3) checks the goal with an SMT solver and applies an axiom to close the proof. *)
  

  (* END BOILERPLATE *)

  Create HintDb list_eqns.

  (* Here we add the behavior of the various coq functions to a hint database.
    In SMT land, these functions are all uninterpreted functions,
    so the SMT solver doesn't have any knowledge about their implementations.
    To recover this information we strengthen the proof goal with
    *equations* about the functional behavior of Coq functions.
  *)

  Hint Resolve app_equation_1 : list_eqns.
  Hint Resolve app_equation_2 : list_eqns.
  Hint Resolve rev_equation_1 : list_eqns.
  Hint Resolve rev_equation_2 : list_eqns.
  Hint Resolve tail_rev_equation_1 : list_eqns.
  Hint Resolve tail_rev_equation_2 : list_eqns.
  Hint Resolve In_equation_1 : list_eqns.
  Hint Resolve In_equation_2 : list_eqns.
  Hint Resolve len_equation_1 : list_eqns.
  Hint Resolve len_equation_2 : list_eqns.
  Hint Resolve NoDup_equation_1 : list_eqns.
  Hint Resolve NoDup_equation_2 : list_eqns.

  (* And that's it! We're on to proofs. *)

  Lemma app_app_one : 
    forall (a: A) (l r : List A), 
      app (app l (a::[])) r = app l (a :: r).
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate app_app_one : list_eqns.

  Lemma app_assoc : 
    forall (x y z: List A),
      app (app x y) z = app x (app y z).
  Proof.
    induction x; mirrorsolve.
  Qed.

  Set MirrorSolve Solver "cvc5".

  Hint Immediate app_assoc : list_eqns.

  Lemma app_nil_r : 
    forall l, app l [] = l.
  Proof.
    induction l; mirrorsolve.
  Qed.

  (* Hint Immediate app_nil_r : list_eqns. *)
  Set MirrorSolve Query Debug.

  Lemma rev_app : 
    forall (l r : List A), 
      ListFuncs.rev (app l r) = app (ListFuncs.rev r) (ListFuncs.rev l).
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate rev_app : list_eqns.

  Lemma rev_rev : 
    forall (l : List A), 
      ListFuncs.rev (ListFuncs.rev l) = l.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate rev_rev : list_eqns.

  Lemma tail_rev_spec : 
    forall (l acc : List A), 
      tail_rev l acc = ListFuncs.app (ListFuncs.rev l) acc.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate tail_rev_spec : list_eqns.

  Lemma tail_rev_sound : 
    forall (l : List A), 
      ListFuncs.rev l = tail_rev l [].
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate tail_rev_sound : list_eqns.

  Lemma app_len : 
    forall (l r : List A), 
      len (app l r) = (len l + len r)%Z.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate app_len : list_eqns.

  Lemma rev_len :
    forall (l: List A), 
      len l = len (ListFuncs.rev l).
  Proof.
    induction l; mirrorsolve.
  Qed.
  
  Hint Immediate rev_len : list_eqns.

  Lemma app_In : 
    forall x l r,
      In x (app l r) <-> In x l \/ In x r.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate app_In : list_eqns.

  Lemma in_rev : 
    forall x l,
      In x l <-> In x (ListFuncs.rev l).
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate in_rev : list_eqns.

  Lemma NoDup_remove :
    forall l l' a, 
    NoDup (app l (a::l')) -> 
    NoDup (app l l') /\ ~In a (app l l').
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate NoDup_remove : list_eqns.

  Lemma NoDup_remove_1 : 
    forall l l' a,  
      NoDup (app l (a::l')) -> NoDup (app l l').
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate NoDup_remove_1 : list_eqns.

  Lemma NoDup_remove_2 : 
    forall l l' a, 
      NoDup (app l (a::l')) -> 
      ~In a (app l l').
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate NoDup_remove_2 : list_eqns.

  Theorem NoDup_cons_iff :
    forall a l, 
      NoDup (a::l) <-> 
      ~ In a l /\ NoDup l.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate NoDup_cons_iff : list_eqns.

  Lemma NoDup_app : 
    forall l1 l2, 
      NoDup (app l1 l2) <-> 
      NoDup l1 /\ NoDup l2 /\ 
      (forall x, In x l1 -> ~ In x l2) /\
      (forall x, In x l2 -> ~ In x l1).
  Proof.
    induction l1; mirrorsolve.
  Qed.

  Hint Immediate NoDup_app : list_eqns.

  Lemma NoDup_rev :
    forall l,
      NoDup l <-> NoDup (ListFuncs.rev l).
  Proof.
    induction l; mirrorsolve.
  Qed.

End ListFuncs.
  

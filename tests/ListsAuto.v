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

(* In this demo we make two different versions of list reverse:
  1) my_rev, which is a naive quadratic list reverse (it uses append at each step, which is linear, on each element of the input)
  2) tail_rev, which is a classic tail-optimized linear list reverse.

  We prove that forall xs, my_rev xs = tail_rev xs using mirrorsolve's proof automation

  To demo the rest of mirrorsolve, we also define a length function, and a custom predicate, and prove properties about them with reverse.
*)

Section ListFuncs.
  Variable (A: Type).
  Unset Universe Polymorphism.

  (* We use a simpler, custom version of lists to make it easier to autogenerate
     plugin configuration. For verification of the same proofs but on normal lists, see tests/Lists.v.
  *)

  Inductive List_A := | nil_A | cons_A : A -> List_A -> List_A.

  Infix "::" := cons_A.
  Notation "[]" := nil_A.

  Inductive Even_list : List_A -> Prop := 
  | even_nil : Even_list []
  | even_cons : 
    forall xs (es: Even_list xs),
      forall x x', Even_list (x :: x' :: xs).

  (* We will make use of a hint database to reflect recursive coq functions into SMT logic.
     For now, don't worry about it, but it's handy to use Equations for recursion to make use of the generated equations.
   *)

  Equations app (l: List_A) (r: List_A) : List_A := {
    app [] r := r;
    app (x :: l') r := x :: app l' r;
  }.

  Check app_equation_1. (* forall r : list A, app [] r = r *)
  Check app_equation_2. (* forall (x : A) (l' r : list A), app (x :: l') r = x :: app l' r *)
  
  Equations rev (xs: List_A) : List_A := {
    rev [] := [];
    rev (x :: l') := app (rev l') (x :: []);
  }.

  Equations tail_rev (xs: List_A) (acc: List_A) : List_A := {
    tail_rev [] acc := acc;
    tail_rev (x :: xs') acc := tail_rev xs' (x :: acc);
  }.

  Equations In (x: A) (l: List_A) : Prop := {
    In x [] := False;
    In x (x' :: l') := x = x' \/ In x l';
  }.

  Lemma In_equation_1' : 
    forall x, ~ In x [].
  Proof.
    intros.
    autorewrite with In.
    intuition eauto.
  Qed.

  Lemma In_equation_2' : 
    forall (x x' : A) (l' : List_A),
      In x (x' :: l') <-> (x = x' \/ In x l').
  Proof.
    intros.
    (* simpl. *)
    autorewrite with In.
    intuition eauto.
  Qed.

  (* For simplicity we use Z instead of nat or N, because Z translates directly to SMT. 
     We could also use nat or N and use the N2Z functor to convert goals from nat/N to Z. 
  *)
  Equations len (xs: List_A) : Z := {
    len [] := 0;
    len (_ :: xs) := len xs + 1;
  }.

  (* Next we set up a first-order logic for lists, app, rev, tail_rev, In, and len.
   *)

  Declare ML Module "mirrorsolve".

  From MetaCoq.Template Require Import All Loader.
  Import MCMonadNotation.
  Require Import MirrorSolve.Config.
  Open Scope bs.

  Notation pack x := (existT _ _ x).

  Universe foo.
  MetaCoq Quote Definition typ_term := Type@{foo}.

  (* TODO: support for inductive relations *)
  MetaCoq Run (
    xs <- add_funs typ_term [
        pack ListFuncs.rev
      ; pack ListFuncs.app
      ; pack ListFuncs.List_A
      ; pack ListFuncs.tail_rev
      ; pack ListFuncs.len
      ; pack Z.add
    ] [ 
        pack ListFuncs.In 
      (* ; pack ListFuncs.Even_list *)
    ];;
    xs' <- tmQuote xs ;;
    tmMkDefinition "trans_tbl" xs'
  ).

  Check tmMkDefinition.

  Check trans_tbl.
    
  MetaCoq Run (
    gen_sig typ_term sorts fol_funs fol_rels
  ).

  (* Next we give a semantics to the function and relation symbols, in terms of the original functions and relation.
    We use equations because the semantics has a dependent type (the sort symbols are interpreted for arguments and results).
    The interpreted arguments are provided in a HList input.
  *)

  Equations interp_fun args ret (f: fol_funs args ret) (hargs : HList.t interp_sorts args) : interp_sorts ret := {
    interp_fun _ _ nil_A_f _ := [];
    interp_fun _ _ cons_A_f (x ::: y ::: hnil) := x :: y;
    interp_fun _ _ app_f (l ::: r ::: hnil):= app l r;
    interp_fun _ _ rev_f (x ::: hnil) := ListFuncs.rev x;
    interp_fun _ _ tail_rev_f (x ::: l ::: hnil) := tail_rev x l;
    interp_fun _ _ len_f (x ::: hnil) := len x;
    interp_fun _ _ add_f (l ::: r ::: hnil) := (l + r)%Z;
    interp_fun _ _ (z_const_f z) hnil := z;
  }.
  
  Equations interp_rel args (r: fol_rels args) (hargs : HList.t interp_sorts args) : Prop := {
    interp_rel _ In_r (x ::: l ::: hnil)  := In x l;
  }.

  (* We can wrap these definitions together with the previous signature to get a first-order logic *model* for mirrorsolve! *)

  Definition fm_model := 
    Build_model sig interp_sorts interp_fun interp_rel.

  (* Next we configure the reflection logic for mirrorsolve. 
    So we're going to connect the first-order logic syntax and semantics with Coq's AST in MetaCoq. 
  *)

  MetaCoq Run (
    add_matches sig fm_model trans_tbl
  ).

  Require Import MirrorSolve.Reflection.Tactics.
  (* TODO: 
    to infer this code, turn the wf condition into a typeclass,
    register a new typeclass instance when we add the z literal to the sig/interpretation,
    and tell TemplateCoq to do typeclass resolution where the ltac is called
  
  *)
  Definition match_tacs' := ((is_z_term, tacLit sig fm_model z_lit (fun x => (sort_Z; x)) (fun x _ => (sort_Z; TFun sig (z_const_f x) hnil)) ltac:(solve_lit_wf)) :: match_tacs)%list.


  Require MirrorSolve.SMTSig.

  MetaCoq Run (
    ctx <- build_printing_ctx sig sort_prop trans_tbl [(pack Z.add, "+"%string)];; 
    ctx' <- tmEval all ctx ;;
    rhs <- tmQuote ctx' ;; 
    tmMkDefinition "fol_theory" rhs
  ).

  Require Import MirrorSolve.Reflection.Tactics.

  Transparent denote_tm.
  Require Import MirrorSolve.Axioms.

  Ltac check_goal_unsat := 
    match goal with 
    | |- ?G => check_unsat_neg_func fol_theory G; eapply UnsoundAxioms.interp_true
    end.

  Create HintDb list_eqns.

  Hint Resolve app_equation_1 : list_eqns.
  Hint Resolve app_equation_2 : list_eqns.
  Hint Resolve rev_equation_1 : list_eqns.
  Hint Resolve rev_equation_2 : list_eqns.
  Hint Resolve tail_rev_equation_1 : list_eqns.
  Hint Resolve tail_rev_equation_2 : list_eqns.
  Hint Resolve In_equation_1' : list_eqns.
  Hint Resolve In_equation_2' : list_eqns.
  Hint Resolve len_equation_1 : list_eqns.
  Hint Resolve len_equation_2 : list_eqns.

  Ltac prep_proof := 
    hints_foreach (fun x => pose proof x) "list_eqns";
    Utils.revert_all;
    unfold "<->" in *.

  Scheme Equality for sorts.

  Ltac quote_reflect_list := quote_reflect sig fm_model sorts_eq_dec match_tacs' match_sorts.
  Ltac quote_extract_list := quote_extract sig fm_model sorts_eq_dec match_tacs' match_sorts.

  Ltac mirrorsolve :=
    prep_proof;
    quote_reflect_list;
    check_goal_unsat.

  Lemma app_app_one : 
    forall (a: A) (l r : List_A), 
      app (ListFuncs.app l (a::[])) r = app l (a :: r).
  Proof.
    induction l; mirrorsolve.
  Qed.


  Hint Immediate app_app_one : list_eqns.

  Lemma app_assoc : 
    forall (x y z: List_A),
      app (app x y) z = app x (app y z).
  Proof.
    induction x; mirrorsolve.
  Qed.

  Hint Immediate app_assoc : list_eqns.

  Lemma app_nil_r : 
    forall l, app l [] = l.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate app_nil_r : list_eqns.

  SetSMTSolver "cvc5".

  Lemma rev_app : 
    forall (l r : List_A), 
      ListFuncs.rev (app l r) = app (ListFuncs.rev r) (ListFuncs.rev l).
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate rev_app : list_eqns.

  Lemma rev_rev : 
    forall (l : List_A), 
      ListFuncs.rev (ListFuncs.rev l) = l.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate rev_rev : list_eqns.

  Lemma tail_rev_spec : 
    forall (l acc : List_A), 
      tail_rev l acc = ListFuncs.app (ListFuncs.rev l) acc.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate tail_rev_spec : list_eqns.

  Lemma tail_rev_sound : 
    forall (l : List_A), 
      ListFuncs.rev l = tail_rev l [].
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate tail_rev_sound : list_eqns.

  Lemma app_len : 
    forall (l r : List_A), 
      len (app l r) = (len l + len r)%Z.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate app_len : list_eqns.

  Lemma rev_len :
    forall (l: List_A), 
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

End ListFuncs.
  
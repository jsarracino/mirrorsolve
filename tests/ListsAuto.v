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

  Inductive List_A := 
  | nil_A 
  | cons_A : A -> List_A -> List_A.

  Infix "::" := cons_A.
  Notation "[]" := nil_A.

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

  Inductive NoDup : List_A -> Prop :=
  | NoDup_nil : NoDup []
  | NoDup_cons : forall x l, 
    ~ In x l -> 
    NoDup l -> 
    NoDup (x::l).

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

  (* Not sure why but all of these MetaCoq statements need to be in separate blocks *)

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
      ; pack ListFuncs.NoDup
    ];;
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
    add_const_wf_instances sig fm_model trans_tbl
  ).
  MetaCoq Run (
    add_matches sig fm_model trans_tbl
  ).
  MetaCoq Run (
    (* This last argument of build_printing_ctx is a list of "overrides" for replacing a Coq term with an SMT primitive.
       In this case, we want to use SMT's integer arithmetic for the implementation of Z.add (instead of treating Z.add like an uninterpreted function),
       so we add an entry in the list of overrides for Z.add and the string "+".
    *)
    ctx <- build_printing_ctx sig sort_prop trans_tbl [
        (pack Z.add, "+"%string)
      ];; 
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
  Hint Resolve NoDup_equation_1 : list_eqns.
  Hint Resolve NoDup_equation_2 : list_eqns.

  Ltac prep_proof := 
    hints_foreach (fun x => pose proof x) "list_eqns";
    Utils.revert_all;
    unfold "<->" in *.

  Scheme Equality for sorts.

  Ltac quote_reflect_list := quote_reflect sig fm_model sorts_eq_dec match_tacs match_sorts.
  Ltac quote_extract_list := quote_extract sig fm_model sorts_eq_dec match_tacs match_sorts.

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
    idtac "tail_rev_sound".
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
    idtac "app_In".
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
    idtac "NoDup_remove".
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
  

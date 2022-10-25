(** * SearchTree: Binary Search Trees 
    Do not commit to version tracking if it has proofs!!
*)

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
    let claim_eq := tApp eq_quoted [hole; claim_lhs; claim_rhs] in
    let claim_quoted := wrap_type (arg_count+depth-1) claim_eq in
    claim <- tmUnquoteTyped Type claim_quoted ;;
    let proof_quoted :=
      wrap_body (arg_count+depth-1) (tApp eq_refl_quoted [hole; claim_rhs]) in
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
    infer_equation arg_type_quoted func_quoted info body.(bbody) depth offset index ;;
    infer_equations_walk_cases arg_type_quoted func_quoted info bodies depth offset (S index)
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
  | tCase info _ (tRel offset) bodies =>
    match nth_error context offset with
    | Some arg_type_quoted =>
      infer_equations_walk_cases arg_type_quoted top_quoted info bodies (List.length context) offset 0
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
End Tests.





(* Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat. *)
Require Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.

(* Definition gtb x y := Nat.ltb y x. *)

(* Infix ">?" := gtb (at level 70). *)

Notation key := Z.
Inductive tree (V : Type) : Type :=
| E
| T (l : tree V) (k : key) (v : V) (r : tree V).

Arguments E {V}.
Arguments T {V}.

Definition empty_tree {V} : tree V := E.

Fixpoint lookup {V} (d : V) (x : key) (t : tree V) : V :=
  match t with
  | E => d
  | T l y v r => 
    if x <? y then lookup d x l
    else if x >? y then lookup d x r
    else v
  end.

Section Foo.
  Variable (V: Type).
  Fixpoint insert (x : key) (v : V) (t : tree V) : tree V :=
    match t with
    | E => T E x v E
    | T l y v' r => 
      if x <? y then T (insert x v l) y v' r
      else if x >? y then T l y v' (insert x v r)
      else T l x v r
    end.
End Foo.

Arguments insert {V}.

Fixpoint ForallT {V} (P: key -> V -> Prop) (t: tree V) : Prop :=
  match t with
  | E => True
  | T l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.

Hint Unfold ForallT.

Inductive BST {V : Type} : tree V -> Prop :=
| BST_E : BST E
| BST_T : forall l x v r,
    ForallT (fun y _ => y < x) l ->
    ForallT (fun y _ => y > x) r ->
    BST l ->
    BST r ->
    BST (T l x v r).

Hint Constructors BST : core.
Hint Constructors BST.
Hint Constructors tree.

(** FULL: Prove that the empty tree is a BST. *)

Require Import MirrorSolve.Crush.
From Hammer Require Import Hammer.

Theorem empty_tree_BST : forall (V : Type),
    BST (@empty_tree V).
Proof.
  auto.
Qed.

(* crush, and hammer all do the first goal here but not the second.
    fo will do the first goal if you manually simplify first.
*)
Theorem insert_BST : forall (V : Type) (t : tree V) (k : key) (v : V) ,
    BST t -> BST (insert k v t).
Proof.
    induction 1.
    -   
        (* firstorder. *)
        (* crush. *)
        (* hammer. *)
        admit.

    -  
        (* firstorder. *)
        (* crush. *)
        (* hammer. *)
        admit.
Admitted.

Theorem lookup_empty : forall (V : Type) (d : V) (k : key),
    lookup d k empty_tree = d.
Proof.
  auto.
Qed.

Lemma lt_false : 
    forall x, x <? x = false.
Proof.
Admitted.

Lemma gt_false : 
    forall x, x >? x = false.
Proof.
Admitted.

(* Hint Rewrite gt_false.
Hint Rewrite lt_false. *)

(* fo, crush, and hammer don't handle either of these. Crush will take the first if you give it hints for reducing gt and lt. 
    Maybe show the proof state?
    *)
Theorem lookup_insert_eq : forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
    lookup d k (insert k v t)  = v.
Proof.
    induction t0.
    -   
        (* firstorder. *)
        (* crush. *)
        (* hammer. *)
        admit.

    -  
        (* firstorder. *)
        (* crush. *)
        (* hammer. *)
        admit.
Admitted.

Theorem lookup_insert_neq :
  forall (V : Type) (t : tree V) (d : V) (k k' : key) (v : V),
   k <> k' -> lookup d k' (insert k v t) = lookup d k' t.
Proof.
Admitted.


Require Import MirrorSolve.BV.
Require Import MirrorSolve.SMT.
Require Import MirrorSolve.UF.

Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.
Require Import MirrorSolve.Reflection.Tactics.

Declare ML Module "mirrorsolve".

From MetaCoq.Template Require Import All Loader.
Import MCMonadNotation.
Require Import MirrorSolve.Config.
Open Scope bs.

Require Import Coq.Lists.List.

Require Import Coq.Strings.String.


Section GT.

  Variable (V: Type).

  Fixpoint gt_t (k: Z) (t: tree V) : Prop :=
    match t with
    | E => True
    | T l k' _ r =>
      k' > k /\ gt_t k l /\ gt_t k r 
    end.

  Definition insert' := Eval compute in @insert V.

  (* MirrorSolve's automation needs this later. *)

  Notation pack x := (existT _ _ x).

  Definition fun_syms : list packed := ([
      pack (tree V)
    ; pack insert'
    ; pack Z.ltb
    ; pack Z.gtb
  ])%type.

  Definition rel_syms : list packed := ([ 
      pack Z.gt
    ; pack gt_t
  ])%type.

  Definition prim_syms : list (packed * String.string) := ([
      (pack Z.lt, "<")
    ; (pack Z.gt, ">")
    ; (pack Z.ltb, "<")
    ; (pack Z.gtb, ">")
  ])%string.

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
  Definition fm_model := FirstOrder.Build_model sig interp_sorts interp_funs interp_rels.
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

  Ltac prep_proof := 
    hints_foreach (fun x => pose proof x) "eqns";
    Utils.revert_all;
    unfold "<->" in *.

  Scheme Equality for sorts.

  Ltac quote_reflect_tree := quote_reflect sig fm_model sorts_eq_dec match_tacs match_sorts.

  Ltac mirrorsolve :=
    timeout 60 (prep_proof;
    quote_reflect_tree;
    check_goal_unsat).

  Set MirrorSolve Solver "z3".

  Create HintDb eqns.
  MetaCoq Run (infer_equations insert').
  Print


  Lemma gt_emp:
  forall x, gt_t x E ↔ True.
    Proof.
      intros; apply iff_refl.
  Qed.
    Lemma gt_node:
      forall k l k’ v r,
  (k’ > k /\ gt_t k l /\ gt_t k r) ↔
        gt_t k (T l k’ v r).
    Proof.
      intros; apply iff_refl.
    Qed.
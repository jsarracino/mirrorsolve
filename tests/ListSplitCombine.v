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
Require Import Coq.Lists.List.

(* 
  This file demonstrates how to use mirrorsolve with nested, predefined inductive types.
  Here we'll prove some facts about the standard library's list split and combine.

  The definitions of split and combine are:

  split = 
fun A B : Type =>
fix split (l : list (A × B)) : list A × list B :=
  match l with
  | [] => ([], [])
  | p :: tl =>
	  let (x, y) := p in
      let (left, right) := split tl in (x :: left, y :: right)
  end
     : forall A B : Type, list (A × B) -> list A × list B

  combine = 
fun A B : Type =>
fix combine (l : list A) (l' : list B) {struct l} : list (A × B) :=
  match l with
  | [] => []
  | x :: tl =>
	  match l' with
      | [] => []
      | y :: tl' => (x, y) :: combine tl tl'
      end
  end
     : forall A B : Type, list A -> list B -> list (A × B)

  We prove the following lemmas:

    Lemma in_split_l : forall (l:list (A*B))(p:A*B),
      In p l -> In (fst p) (fst (split l)).

    Lemma in_split_r : forall (l:list (A*B))(p:A*B),
      In p l -> In (snd p) (snd (split l)).

    Lemma split_nth : forall (l:list (A*B))(n:nat)(d:A*B),
      nth n l d = (nth n (fst (split l)) (fst d), nth n (snd (split l)) (snd d)).

    Lemma split_length_l : forall (l:list (A*B)),
      length (fst (split l)) = length l.

    Lemma split_length_r : forall (l:list (A*B)),
      length (snd (split l)) = length l.

    Lemma split_combine : forall (l: list (A*B)),
      forall l1 l2, split l = (l1, l2) -> combine l1 l2 = l.

    Lemma combine_split : forall (l:list A)(l':list B), length l = length l' ->
      split (combine l l') = (l,l').

    Lemma in_combine_l : forall (l:list A)(l':list B)(x:A)(y:B),
      In (x,y) (combine l l') -> In x l.

    Lemma in_combine_r : forall (l:list A)(l':list B)(x:A)(y:B),
      In (x,y) (combine l l') -> In y l'.

    Lemma combine_length : forall (l:list A)(l':list B),
      length (combine l l') = min (length l) (length l').

    Lemma combine_nth : forall (l:list A)(l':list B)(n:nat)(x:A)(y:B),
      length l = length l' ->
      nth n (combine l l') (x,y) = (nth n l x, nth n l' y).
*)

(* We need to work in Z, so we reimplement nth and length using Z instead of nat *)

Fixpoint nth_z {T} (i: Z) (xs: list T) (d: T) := 
  match xs with
  | [] => d
  | x :: xs' => 
    ite (Z.eqb i 0) x (nth_z (i - 1) xs' d)
  end.

Fixpoint length_z {T} (xs: list T) := 
  match xs with 
  | [] => 0%Z
  | x :: xs' => (1 + length_z xs')%Z
  end.

Section ListSplitCombine.

  Unset Universe Polymorphism.
  (* We need type parameters to be section variables: *)
  Variable (A: Type).
  Variable (B: Type).

  (* We need to reflect:
    A * B, fst, snd
    list A,
    list B,
    list (A * B),
    @In A,
    @In B,
    @In (A * B)
    @split A B,
    @combine A B,
    @option (A * B)/A/B
    nth (we will reimplement with Z, for A/B/A*B)
    length (also reimplement with Z, for A/B/A*B)
    in Z:
      +, -, leb, ge, eqb, min
  *)

  Declare ML Module "mirrorsolve".

  From MetaCoq.Template Require Import All Loader.
  Import MCMonadNotation.
  Require Import MirrorSolve.Config.
  Open Scope bs.

  Universe foo.
  MetaCoq Quote Definition typ_term := Type@{foo}.
  Notation pack x := (existT _ _ x).

  Definition fun_syms : list packed := [
      pack (A * B)%type
    ; pack (list A * list B)%type
    ; pack (@fst A B)
    ; pack (@snd A B)
    ; pack (@fst (list A) (list B))
    ; pack (@snd (list A) (list B))
    ; pack (list A)
    ; pack (list B)
    ; pack (list (A * B))%type
    ; pack (@split A B)
    ; pack (@combine A B)
    ; pack (option (A * B))%type
    ; pack (option A)%type
    ; pack (option B)%type
    ; pack (@nth_z A)
    ; pack (@nth_z B)
    ; pack (@nth_z (A * B))
    ; pack (@length_z A)
    ; pack (@length_z B)
    ; pack (@length_z (A * B))
    ; pack (Z.add)
    ; pack (Z.sub)
    ; pack (Z.min)
    ; pack (Z.eqb)
    ; pack (@ite A)
    ; pack (@ite B)
    ; pack (@ite (A * B))
    ; pack (@ite Z)
    ; pack Z.leb
  ].

  Definition rel_syms : list packed := [ 
      pack (@In A)
    ; pack (@In B)
    ; pack (@In (A * B))
    ; pack Z.ge
  ].

  Definition prim_syms : list (packed * String.string) := [
      (pack Z.add, "+"%string)
    ; (pack Z.sub, "-"%string)
    ; (pack Z.ge, ">="%string)
    ; (pack Z.eqb, "="%string)
    ; (pack (@ite A), "ite"%string)
    ; (pack (@ite B), "ite"%string)
    ; (pack (@ite (A * B)), "ite"%string)
    ; (pack (@ite Z), "ite"%string)
    ; (pack Z.leb, "<="%string)
  ].

  (* The rest of the automation is copy-paste and should not change between developments. *)
  (* I'm not sure why but all of these MetaCoq statements need to be in separate blocks *)

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

  Eval vm_compute in Utils.flip (trans_tbl.(mp_consts)).
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
    ctx <- build_printing_ctx sig sort_prop trans_tbl prim_syms;; 
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

  Ltac prep_proof := 
    hints_foreach (fun x => pose proof x) "list_eqns";
    Utils.revert_all;
    unfold "<->" in *.

  Scheme Equality for sorts.

  (* A wrapper around MirrorSolve's reflection tactic. *)
  Ltac quote_reflect_list := quote_reflect sig fm_model sorts_eq_dec match_tacs match_sorts.

  Ltac mirrorsolve :=
    prep_proof; 
    quote_reflect_list; 
    check_goal_unsat. 

  Lemma fst_A_eqn: 
    forall (x: A) (y: B), 
      fst (x, y) = x.
  Proof.
    intuition eauto.
  Qed.

  Lemma snd_B_eqn: 
    forall (x: A) (y: B), 
      snd (x, y) = y.
  Proof.
    intuition eauto.
  Qed.

  Hint Resolve fst_A_eqn : list_eqns.
  Hint Resolve snd_B_eqn : list_eqns.

  Lemma fst_LA_eqn: 
    forall (x: list A) (y: list B), 
      fst (x, y) = x.
  Proof.
    intuition eauto.
  Qed.

  Lemma snd_LB_eqn: 
    forall (x: list A) (y: list B), 
      snd (x, y) = y.
  Proof.
    intuition eauto.
  Qed.

  Hint Resolve fst_LA_eqn : list_eqns.
  Hint Resolve snd_LB_eqn : list_eqns.


  Lemma In_A_eqn_1:
    forall x, 
    @In A x [] <-> False.
  Proof.
    intuition eauto.
  Qed.

  Lemma In_A_eqn_2:
    forall x x' xs, 
    @In A x (x' :: xs) <-> x = x' \/ In x xs.
  Proof.
    simpl;
    intuition eauto.
  Qed.

  Hint Resolve In_A_eqn_1 : list_eqns.
  Hint Resolve In_A_eqn_2 : list_eqns.

  Lemma In_B_eqn_1:
    forall x, 
    @In B x [] <-> False.
  Proof.
    intuition eauto.
  Qed.

  Lemma In_B_eqn_2:
    forall x x' xs, 
    @In B x (x' :: xs) <-> x = x' \/ In x xs.
  Proof.
    simpl;
    intuition eauto.
  Qed.

  Hint Resolve In_B_eqn_1 : list_eqns.
  Hint Resolve In_B_eqn_2 : list_eqns.

  Lemma In_AB_eqn_1:
    forall x, 
    @In (A * B) x [] <-> False.
  Proof.
    intuition eauto.
  Qed.

  Lemma In_AB_eqn_2:
    forall x x' xs, 
    @In (A * B) x (x' :: xs) <-> x = x' \/ In x xs.
  Proof.
    simpl;
    intuition eauto.
  Qed.

  Hint Resolve In_AB_eqn_1 : list_eqns.
  Hint Resolve In_AB_eqn_2 : list_eqns.

  (* | [] => ([], []) *)
  Lemma split_eqn_1 : 
    @split A B [] = ([], []).
  Proof.
    intuition eauto.
  Qed.

  (* | (x,y) :: tl => let (left,right) := split tl in (x::left, y::right) *)
  (* This one is a bit tricky because our SMT reflection doesn't have pattern matching, 
     so instead we use fst and snd (for which we have uninterpreted functions). *)
  Lemma split_eqn_2 : 
    forall x y tl, 
      @split A B ((x,y) :: tl) = (x :: fst (split tl), y :: snd (split tl)).
  Proof.
    intros.
    simpl.
    destruct (split tl).
    exact eq_refl.
  Qed.

  Hint Immediate split_eqn_1 : list_eqns.
  Hint Immediate split_eqn_2 : list_eqns.

  (* Sadly we need equations for each instantiation of length_z, 
     i.e. length_z A, length_z B, and length_z (A * B)  
  *)
  Lemma length_z_A_eqn_1 : 
    @length_z A [] = 0%Z.
  Proof.
    intuition eauto.
  Qed.

  Lemma length_z_A_eqn_2 : 
    forall x xs, 
    @length_z A (x :: xs) = (1 + length_z xs)%Z.
  Proof.
    intuition eauto.
  Qed.

  Hint Immediate length_z_A_eqn_1 : list_eqns.
  Hint Immediate length_z_A_eqn_2 : list_eqns.

  Lemma length_z_B_eqn_1 : 
    @length_z B [] = 0%Z.
  Proof.
    intuition eauto.
  Qed.

  Lemma length_z_B_eqn_2 : 
    forall x xs, 
    @length_z B (x :: xs) = (1 + length_z xs)%Z.
  Proof.
    intuition eauto.
  Qed.

  Hint Immediate length_z_B_eqn_1 : list_eqns.
  Hint Immediate length_z_B_eqn_2 : list_eqns.

  Lemma length_z_AB_eqn_1 : 
    @length_z (A * B)%type [] = 0%Z.
  Proof.
    intuition eauto.
  Qed.

  Lemma length_z_AB_eqn_2 : 
    forall x xs, 
    @length_z (A * B)%type (x :: xs) = (1 + length_z xs)%Z.
  Proof.
    intuition eauto.
  Qed.

  Hint Immediate length_z_AB_eqn_1 : list_eqns.
  Hint Immediate length_z_AB_eqn_2 : list_eqns.


  (* combine [] _ = [] *)
  Lemma combine_eqn_1 : 
    forall bs, 
    @combine A B [] bs = [].
  Proof.
    intuition eauto.
  Qed.

  (* combine _ [] = [] *)
  Lemma combine_eqn_2 : 
    forall xs, 
    @combine A B xs [] = [].
  Proof.
    induction xs; intuition eauto.
  Qed.

  (* combine (x :: xs) (y :: ys) = (x, y) :: combine xs ys *)
  Lemma combine_eqn_3 : 
    forall x xs y ys, 
    @combine A B (x :: xs) (y :: ys) = (x, y) :: combine xs ys.
  Proof.
    intuition eauto.
  Qed.

  (* A quirk of reflecting functions that use Z instead of N/nat is that 
     we need to manually reflect the fact that they are nonnegative.  
     However! We can use mirrorsolve to prove this fact.
  *)
  Lemma length_z_A_nonneg: 
    forall x, 
      (@length_z A x >= 0)%Z.
  Proof.
    induction x;
    mirrorsolve.
  Qed.

  Lemma length_z_B_nonneg: 
    forall x, 
      (@length_z B x >= 0)%Z.
  Proof.
    induction x;
    mirrorsolve.
  Qed.

  Lemma length_z_AB_nonneg: 
    forall x, 
      (@length_z (A*B)%type x >= 0)%Z.
  Proof.
    induction x;
    mirrorsolve.
  Qed.

  Hint Immediate length_z_A_nonneg : list_eqns.
  Hint Immediate length_z_B_nonneg : list_eqns.
  Hint Immediate length_z_AB_nonneg : list_eqns.

  Lemma nth_z_A_eqn_1 : 
    forall n d, 
      @nth_z A n nil d = d.
  Proof.
    intuition eauto.
  Qed.

  Lemma nth_z_A_eqn_2 : 
    forall n x xs d, 
      @nth_z A n (x :: xs) d = 
        ite (Z.eqb n 0) x (nth_z (n - 1) xs d).
  Proof.
    intuition eauto.
  Qed.

  Hint Immediate nth_z_A_eqn_1 : list_eqns.
  Hint Immediate nth_z_A_eqn_2 : list_eqns.

  Lemma nth_z_B_eqn_1 : 
    forall n d, 
      @nth_z B n nil d = d.
  Proof.
    intuition eauto.
  Qed.

  Lemma nth_z_B_eqn_2 : 
    forall n x xs d, 
      @nth_z B n (x :: xs) d = 
        ite (Z.eqb n 0) x (nth_z (n - 1) xs d).
  Proof.
    intuition eauto.
  Qed.

  Hint Immediate nth_z_B_eqn_1 : list_eqns.
  Hint Immediate nth_z_B_eqn_2 : list_eqns.

  Lemma nth_z_AB_eqn_1 : 
    forall n d, 
      @nth_z (A * B)%type n nil d = d.
  Proof.
    intuition eauto.
  Qed.

  Lemma nth_z_AB_eqn_2 : 
    forall n x xs d, 
      @nth_z (A * B)%type n (x :: xs) d = 
        ite (Z.eqb n 0) x (nth_z (n - 1) xs d).
  Proof.
    intuition eauto.
  Qed.

  Hint Immediate nth_z_AB_eqn_1 : list_eqns.
  Hint Immediate nth_z_AB_eqn_2 : list_eqns.



  (* actual proofs *)

  Lemma split_length_l : forall (l:list (A*B)),
    length_z (fst (split l)) = length_z l.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate split_length_l : list_eqns.
  
  Lemma split_length_r : forall (l:list (A*B)),
    length_z (snd (split l)) = length_z l.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate split_length_r : list_eqns.

  Lemma in_split_l : forall (l:list (A*B))(p:A*B),
    In p l -> In (fst p) (fst (split l)).
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate in_split_l : list_eqns.

  Lemma in_split_r : forall (l:list (A*B))(p:A*B),
    In p l -> In (snd p) (snd (split l)).
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate in_split_r : list_eqns.

  Hint Immediate combine_eqn_1 : list_eqns.
  Hint Immediate combine_eqn_2 : list_eqns.
  Hint Immediate combine_eqn_3 : list_eqns.

  Lemma split_combine : forall (l: list (A*B)),
    forall l1 l2, split l = (l1, l2) -> combine l1 l2 = l.
  Proof.
    induction l;
    mirrorsolve.
  Qed.

  Hint Immediate split_combine : list_eqns.

  Lemma combine_split : forall (l:list A)(l':list B), length_z l = length_z l' ->
    split (combine l l') = (l,l').
  Proof.
    induction l; 
    induction l';
    mirrorsolve.
  Qed.

  Hint Immediate combine_split : list_eqns.

  Lemma in_combine_l : forall (l:list A)(l':list B)(x:A)(y:B),
    In (x,y) (combine l l') -> In x l.
  Proof.
    induction l;
    induction l';
    mirrorsolve.
  Qed.

  Hint Immediate in_combine_l : list_eqns.

  Lemma in_combine_r : forall (l:list A)(l':list B)(x:A)(y:B),
    In (x,y) (combine l l') -> In y l'.
  Proof.
    induction l;
    induction l';
    mirrorsolve.
  Qed.

  Hint Immediate in_combine_r : list_eqns.

  Lemma split_nth : forall (l:list (A*B))(n:Z)(d:A*B),
    nth_z n l d = (nth_z n (fst (split l)) (fst d), nth_z n (snd (split l)) (snd d)).
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate split_nth : list_eqns.

  Lemma combine_nth : forall (l:list A)(l':list B)(n:Z)(x:A)(y:B),
    length_z l = length_z l' ->
    nth_z n (combine l l') (x,y) = (nth_z n l x, nth_z n l' y).
  Proof.
    induction l;
    induction l';
    mirrorsolve.
  Qed.

  Hint Immediate combine_nth : list_eqns.

  (* an intermediate lemma that we prove to reflect the behavior of min to SMT *)
  Lemma min_ite : 
    forall n m,
      Z.min n m = ite (Z.leb n m) n m.
  Proof.
    intros.
    destruct (n <=? m)%Z eqn:?;
    simpl;
    Lia.lia.
  Qed.

  Hint Immediate min_ite : list_eqns.

  Lemma combine_length : forall (l:list A)(l':list B),
    length_z (combine l l') = Z.min (length_z l) (length_z l').
  Proof.
    induction l;
    induction l';
    mirrorsolve.
  Qed.

End ListSplitCombine.
  

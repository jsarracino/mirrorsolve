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
*)

(* We need to work in Z, so we reimplement nth and length using Z instead of nat *)

Fixpoint nth_z {T} (i: Z) (xs: list T) (d: T) := 
  match xs with
  | [] => d
  | x :: xs' => 
    if Z.eqb i 0 then x else nth_z (i - 1) xs' d
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
    @split A,
    @option (A * B)
    nth (we will reimplement with Z)
    length (also reimplement with Z)
    in Z:
      plus, minus, and eqb
  *)

  Lemma fst_eqn: 
    forall (x: A) (y: B), 
      fst (x, y) = x.
  Proof.
    intuition eauto.
  Qed.

  Lemma snd_eqn: 
    forall (x: A) (y: B), 
      snd (x, y) = y.
  Proof.
    intuition eauto.
  Qed.

  Declare ML Module "mirrorsolve".

  From MetaCoq.Template Require Import All Loader.
  Import MCMonadNotation.
  Require Import MirrorSolve.Config.
  Open Scope bs.

  Universe foo.
  MetaCoq Quote Definition typ_term := Type@{foo}.
  Notation pack x := (existT _ _ x).

  (* We need to reflect:
    A * B, fst, snd
    list A,
    list B,
    list (A * B),
    @In A,
    @In B,
    @In (A * B)
    @split A,
    @option (A * B)
    nth (we will reimplement with Z)
    length (also reimplement with Z)
    in Z:
      plus, minus, and eqb
  *)
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
    (* ; pack (Z.eqb) *)
  ].

  Definition rel_syms : list packed := [ 
      (* pack (@In A)
    ; pack (@In B)
    ; pack (@In (A * B)) *)
  ].

  Definition prim_syms : list (packed * String.string) := [
      (pack Z.add, "+"%string)
    ; (pack Z.sub, "-"%string)
    (* ; (pack Z.eqb, "="%string) *)
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
  MetaCoq Run (
    add_const_wf_instances sig fm_model trans_tbl
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

  Hint Resolve fst_eqn : list_eqns.
  Hint Resolve snd_eqn : list_eqns.

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

  (* We need to reflect equations for:
    @In A,
    @In B,
    @In (A * B)

    @split A B,
    @combine A B,
    nth_z
    length_z 
  *)

  (* | [] => ([], []) *)
  Lemma split_eqn_1 : 
    (@nil A, @nil B) = (@nil A, @nil B).
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

  (* Hint Immediate split_eqn_1 : list_eqns. *)
  (* Hint Immediate split_eqn_2 : list_eqns. *)

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

  (* Hint Immediate length_z_A_eqn_1 : list_eqns. *)
  (* Hint Immediate length_z_A_eqn_2 : list_eqns. *)

  Lemma split_length_l : 
    @nil A = [].
  Proof.
    prep_proof.
    quote_reflect_list.
    mirrorsolve.

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

  Lemma split_length_l : forall (l:list (A*B)),
    l = l.
  Proof.
    induction l.
    - quote_reflect_list.
      admit.
    - Utils.revert_all.
      quote_reflect_list.
    quote_reflect_list.
    mirrorsolve.

  Lemma split_length_r : forall (l:list (A*B)),
    length (snd (split l)) = length l.



  (* Lemma in_split_l : forall (l:list (A*B))(p:A*B),
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
    nth n (combine l l') (x,y) = (nth n l x, nth n l' y). *)

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
  

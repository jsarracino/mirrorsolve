(** * SearchTree: Binary Search Trees 
    Do not commit to version tracking if it has proofs!!
*)
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Open Scope nat_scope.

Definition gtb x y := Nat.ltb y x.

Infix ">?" := gtb (at level 70).

Definition key := nat.
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

Fixpoint insert {V} (x : key) (v : V) (t : tree V) : tree V :=
  match t with
  | E => T E x v E
  | T l y v' r => 
    if x <? y then T (insert x v l) y v' r
    else if x >? y then T l y v' (insert x v r)
    else T l x v r
  end.

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
    induction t;
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
    induction t.
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

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*     Xavier Leroy and Damien Doligez, INRIA Paris-Rocquencourt       *)
(*     Andrew W. Appel, Princeton University                           *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Applicative finite maps are the main data structure used in this
  project.  A finite map associates data to keys.  The two main operations
  are [set k d m], which returns a map identical to [m] except that [d]
  is associated to [k], and [get k m] which returns the data associated
  to key [k] in map [m].  In this library, we distinguish two kinds of maps:
- Trees: the [get] operation returns an option type, either [None]
  if no data is associated to the key, or [Some d] otherwise.
- Maps: the [get] operation always returns a data.  If no data was explicitly
  associated with the key, a default data provided at map initialization time
  is returned.

  In this library, we provide efficient implementations of trees and
  maps whose keys range over the type [positive] of binary positive
  integers or any type that can be injected into [positive].  The
  implementation is based on radix-2 search trees (uncompressed
  Patricia trees) and guarantees logarithmic-time operations.  An
  inefficient implementation of maps as functions is also provided.
*)

(* To avoid useless definitions of inductors in extracted code. *)

Unset Implicit Arguments.

Require Import MirrorSolve.FirstOrder.

Require Import MirrorSolve.BV.
Require Import MirrorSolve.SMT.
Require Import MirrorSolve.UF.

Require Import MirrorSolve.HLists.
Require Import Coq.Lists.List.

Import HListNotations.
Import ListNotations.

Require Import Coq.Strings.String.

Require Import Coq.ZArith.BinInt.
Import HListNotations.

Require Import MirrorSolve.BV.
Require Import MirrorSolve.SMT.
Require Import MirrorSolve.UF.

Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.
Require Import MirrorSolve.Reflection.Tactics.
Require Import MirrorSolve.Automation.Equations.
From Hammer Require Import Hammer.

Require Import MirrorSolve.Crush.

Require Import MirrorSolve.Hyps.

Ltac hammer' := 
  (* try now (timeout 60 hammer). *)
  idtac.
Ltac crush' := 
  (* try now (timeout 60 crush). *)
  idtac.


(** * An implementation of trees over type [positive] *)

Section PTree.
  Definition elt := positive.
  Definition elt_eq := Pos.eq_dec.

(** ** Representation of trees *)

(** The type [tree'] of nonempty trees.  Each constructor is of the form
    [NodeXYZ], where the bit [X] says whether there is a left subtree,
    [Y] whether there is a value at this node, and [Z] whether there is
    a right subtree. *)

  Inductive tree' (A: Type) : Type := 
  | Node001: tree' A -> tree' A
  | Node010: A -> tree' A
  | Node011: A -> tree' A -> tree' A
  | Node100: tree' A -> tree' A
  | Node101: tree' A -> tree' A ->tree' A
  | Node110: tree' A -> A -> tree' A
  | Node111: tree' A -> A -> tree' A -> tree' A.

  Inductive tree (A: Type) : Type := 
  | Empty : tree A
  | Nodes: tree' A -> tree A.

  Arguments Node001 {A} _.
  Arguments Node010 {A} _.
  Arguments Node011 {A} _ _.
  Arguments Node100 {A} _.
  Arguments Node101 {A} _ _.
  Arguments Node110 {A} _ _.
  Arguments Node111 {A} _ _ _.

  Arguments Empty {A}.
  Arguments Nodes {A} _.

  (* Scheme tree'_ind := Induction for tree' Sort Prop. *)

  Variable (A: Type).

  (** A smart constructor for type [tree]: given a (possibly empty)
      left subtree, a (possibly absent) value, and a (possibly empty)
      right subtree, it builds the corresponding tree. *)

  Equations Node (l: tree A) (o: option A) (r: tree A) : tree A := {
    Node Empty None Empty := Empty;
    Node Empty None (Nodes r') := Nodes (Node001 r');
    Node Empty (Some x) Empty := Nodes (Node010 x);
    Node Empty (Some x) (Nodes r') := Nodes (Node011 x r');
    Node (Nodes l') None Empty := (Nodes (Node100 l'));
    Node (Nodes l') None (Nodes r') := Nodes (Node101 l' r');
    Node (Nodes l') (Some x) Empty := Nodes (Node110 l' x);
    Node (Nodes l') (Some x) (Nodes r') := Nodes (Node111 l' x r');
  }.
  
(** ** Basic operations: [empty], [get], [set], [remove] *)

  Equations empty : tree A := empty := Empty.

  Equations get' (p: positive) (m: tree' A ) : option A := {
    get' (xH) (Node001 _) := None;
    get' (xH) (Node010 x) := Some x;
    get' (xH) (Node011 x _) := Some x;
    get' (xH) (Node100 _) := None;
    get' (xH) (Node101 _ _) := None;
    get' (xH) (Node110 _ x) := Some x;
    get' (xH) (Node111 _ x _) := Some x;
    get' (xO q) (Node001 _) := None;
    get' (xO q) (Node010 _) := None;
    get' (xO q) (Node011 _ _) := None;
    get' (xO q) (Node100 m') := get' q m';
    get' (xO q) (Node101 m' _) := get' q m';
    get' (xO q) (Node110 m' _) := get' q m';
    get' (xO q) (Node111 m' _ _) := get' q m';
    get' (xI q) (Node001 m') := get' q m';
    get' (xI q) (Node010 _) := None;
    get' (xI q) (Node011 _ m') := get' q m';
    get' (xI q) (Node100 m') := None;
    get' (xI q) (Node101 _ m') := get' q m';
    get' (xI q) (Node110 _ _) := None;
    get' (xI q) (Node111 _ _ m') := get' q m';
  }.
    
  Equations get (p: positive) (m: tree A) : option A := {
    get _ Empty := None;
    get p (Nodes m') := get' p m';
  }.

  (** [set0 p x] constructs the singleton tree that maps [p] to [x]
      and has no other bindings. *)

  Equations set0 (p: positive) (x: A) : tree' A := {
    set0 (xH) x := Node010 x;
    set0 (xO q) x := Node100 (set0 q x);
    set0 (xI q) x := Node001 (set0 q x);
  }.

  Equations set' (p: positive) (x: A) (m: tree' A) : tree' A := {
    set' (xH) x (Node001 r) := Node011 x r;
    set' (xH) x (Node010 _) := Node010 x;
    set' (xH) x (Node011 _ r) := Node011 x r;
    set' (xH) x (Node100 l) := Node110 l x;
    set' (xH) x (Node101 l r) := Node111 l x r;
    set' (xH) x (Node110 l _) := Node110 l x;
    set' (xH) x (Node111 l _ r) := Node111 l x r;
    set' (xO q) x (Node001 r) := Node101 (set0 q x) r;
    set' (xO q) x (Node010 y) := Node110 (set0 q x) y;
    set' (xO q) x (Node011 y r) := Node111 (set0 q x) y r;
    set' (xO q) x (Node100 l) := Node100 (set' q x l);
    set' (xO q) x (Node101 l r) := Node101 (set' q x l) r;
    set' (xO q) x (Node110 l y) := Node110 (set' q x l) y;
    set' (xO q) x (Node111 l y r) := Node111 (set' q x l) y r;
    set' (xI q) x (Node001 r) := Node001 (set' q x r);
    set' (xI q) x (Node010 y) := Node011 y (set0 q x);
    set' (xI q) x (Node011 y r) := Node011 y (set' q x r);
    set' (xI q) x (Node100 l) := Node101 l (set0 q x);
    set' (xI q) x (Node101 l r) := Node101 l (set' q x r);
    set' (xI q) x (Node110 l y) := Node111 l y (set0 q x);
    set' (xI q) x (Node111 l y r) := Node111 l y (set' q x r);
  }.
  
  Equations set (p: positive) (x: A) (m: tree A) : tree A := {
    set p x Empty := Nodes (set0 p x);
    set p x (Nodes m') := Nodes (set' p x m');
  }.

  (** Removal in a nonempty tree produces a possibly empty tree.
      To simplify the code, we use the [Node] smart constructor in the
      cases where the result can be empty or nonempty, depending on the
      results of the recursive calls. *)

  Equations rem' (p: positive) (m: tree' A) : tree A := {
    rem' (xH) (Node001 r) := Nodes (Node001 r);
    rem' (xH) (Node010 _) := Empty;
    rem' (xH) (Node011 _ r) := Nodes (Node001 r);
    rem' (xH) (Node100 l) := Nodes (Node100 l);
    rem' (xH) (Node101 l r) := Nodes (Node101 l r);
    rem' (xH) (Node110 l _) := Nodes (Node100 l);
    rem' (xH) (Node111 l _ r) := Nodes (Node101 l r);
    rem' (xO q) (Node001 r) := Nodes (Node001 r);
    rem' (xO q) (Node010 y) := Nodes (Node010 y);
    rem' (xO q) (Node011 y r) := Nodes (Node011 y r);
    rem' (xO q) (Node100 l) := Node (rem' q l) None Empty;
    rem' (xO q) (Node101 l r) := Node (rem' q l) None (Nodes r);
    rem' (xO q) (Node110 l y) := Node (rem' q l) (Some y) Empty;
    rem' (xO q) (Node111 l y r) := Node (rem' q l) (Some y) (Nodes r);
    rem' (xI q) (Node001 r) := Node Empty None (rem' q r);
    rem' (xI q) (Node010 y) := Nodes (Node010 y);
    rem' (xI q) (Node011 y r) := Node Empty (Some y) (rem' q r);
    rem' (xI q) (Node100 l) := Nodes (Node100 l);
    rem' (xI q) (Node101 l r) := Node (Nodes l) None (rem' q r);
    rem' (xI q) (Node110 l y) := Nodes (Node110 l y);
    rem' (xI q) (Node111 l y r) := Node (Nodes l) (Some y) (rem' q r);
  }.

  Equations remove' (p: positive) (m: tree' A) : tree A := remove' := rem'.

  Equations remove (p: positive) (m: tree A) : tree A := {
    remove p Empty := Empty;
    remove p (Nodes m') := remove' p m';
  }.

  Definition not_trivially_empty (l: tree A) (o: option A) (r: tree A) :=
    match l, o, r with
    | Empty, None, Empty => False
    | _, _, _ => True
    end.

  (* MetaCoq Run (infer_equations not_trivially_empty). *)

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma not_trivially_empty_equation_1 : 
    not_trivially_empty Empty None Empty <-> False.
  Proof.
    intuition eauto.
  Qed.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma not_trivially_empty_equation_2 : 
    forall x y z, 
    not_trivially_empty x (Some y) z <-> True.
  Proof.
    destruct x; 
    destruct z;
    intuition eauto.
  Qed.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma not_trivially_empty_equation_3 : 
    forall x y z, 
    not_trivially_empty (Nodes x) y z <-> True.
  Proof.
    destruct y; 
    destruct z;
    intuition eauto.
  Qed.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma not_trivially_empty_equation_4 : 
    forall x y z, 
    not_trivially_empty x y (Nodes z) <-> True.
  Proof.
    destruct x; 
    destruct y;
    intuition eauto.
  Qed.

  Variable (B: Type)
          (empty_b: B)
          (node: tree A -> option A -> tree A -> B).

  Definition node' := node.
  Definition empty' := empty_b.

  Equations tree_case (m: tree A) : B := {
    tree_case (Empty) := empty';
    tree_case (Nodes (Node001 r)) := node' Empty None (Nodes r);
    tree_case (Nodes (Node010 x)) := node' Empty (Some x) Empty;
    tree_case (Nodes (Node011 x r)) := node' Empty (Some x) (Nodes r);
    tree_case (Nodes (Node100 l)) := node' (Nodes l) None Empty;
    tree_case (Nodes (Node101 l r)) := node' (Nodes l) None (Nodes r);
    tree_case (Nodes (Node110 l x)) := node' (Nodes l) (Some x) Empty;
    tree_case (Nodes (Node111 l x r)) := node' (Nodes l) (Some x) (Nodes r);
  }.

  Variable (node_rec: tree A -> B -> option A -> tree A -> B -> B).
  Definition node_rec' := node_rec.

  Equations tree'_rec' (m: tree' A) : B := {
    tree'_rec' (Node001 r) := node_rec' Empty empty' None (Nodes r) (tree'_rec' r);
    tree'_rec' (Node010 x) := node_rec' Empty empty' (Some x) Empty empty';
    tree'_rec' (Node011 x r) := node_rec' Empty empty' (Some x) (Nodes r) (tree'_rec' r);
    tree'_rec' (Node100 l) := node_rec' (Nodes l) (tree'_rec' l) None Empty empty';
    tree'_rec' (Node101 l r) := node_rec' (Nodes l) (tree'_rec' l) None (Nodes r) (tree'_rec' r);
    tree'_rec' (Node110 l x) := node_rec' (Nodes l) (tree'_rec' l) (Some x) Empty empty';
    tree'_rec' (Node111 l x r) := node_rec' (Nodes l) (tree'_rec' l) (Some x) (Nodes r) (tree'_rec' r);
  }.

  Equations tree_rec' (m: tree A) : B := {
    tree_rec' Empty := empty';
    tree_rec' (Nodes m') := tree'_rec' m';
  }.

  Fixpoint prev_append (i j: positive) {struct i} : positive :=
    match i with
      | xH => j
      | xI i' => prev_append i' (xI j)
      | xO i' => prev_append i' (xO j)
    end.

  Definition prev (i: positive) : positive :=
    prev_append i xH.

  Variable beqA: A -> A -> bool.
  Definition beqA' := beqA.

  Equations beq' (m1 m2: tree' A) : bool := {
    beq' (Node001 r1) (Node001 r2) := beq' r1 r2;
    beq' (Node010 x1) (Node010 x2) := beqA' x1 x2;
    beq' (Node011 x1 r1) (Node011 x2 r2) := beqA' x1 x2 && beq' r1 r2;
    beq' (Node100 l1) (Node100 l2) := beq' l1 l2;
    beq' (Node101 l1 r1) (Node101 l2 r2) := beq' l1 l2 && beq' r1 r2;
    beq' (Node110 l1 x1) (Node110 l2 x2) := beqA' x1 x2 && beq' l1 l2;
    beq' (Node111 l1 x1 r1) (Node111 l2 x2 r2 ) := beqA' x1 x2 && beq' l1 l2 && beq' r1 r2;
    beq' (_) (_) := false;
  }.

  (* Note: there are 49 (!!!) equations for beq' *)

  Equations beq (m1 m2: tree A) : bool := {
    beq Empty Empty := true;
    beq (Nodes m1') (Nodes m2') := beq' m1' m2';
    beq _ _ := false
  }.
  (* Note, there are 4 equations for beq *)

  Equations beq_optA (o1 o2: option A) : bool := {
    beq_optA (None) (None) := true;
    beq_optA (Some a1) (Some a2) := beqA' a1 a2;
    beq_optA (_) (_) := false;
  }.
   (* Note, there are 4 equations for beq_optA *)

   (*** MS EFFORT {"type": "definition"} *)
   Equations Pos_eqb (p1 : positive) (p2: positive) : bool := {
    Pos_eqb (xI l) (xI r) := Pos_eqb l r ;
    Pos_eqb (xO l) (xO r) := Pos_eqb l r ;
    Pos_eqb xH xH := true;
    Pos_eqb _ _ := false;
   }.

  (* Note, there are 9 equations for Pos_eqb *)


  (*** MS EFFORT {"type": "definition"} *)
  Definition get_pos_default (i: positive) (x: option A) (l r: tree A) : option A := 
    match i with 
    | xH => x 
    | xO j => get j l
    | xI j => get j r
    end.

  Definition get_eq_bool x m1 m2 := 
    match get x m1, get x m2 with
    | None, None => True
    | Some y1, Some y2 =>  beqA' y1 y2 = true
    | _, _ => False
    end.

  Variable (f_pos : positive -> A -> B).
  Definition f_pos_sym i a := f_pos i a.

  Variable (f: A -> B).
  Definition f_sym a := f a.

  Fixpoint map' (m: tree' A) (i: positive)
      {struct m} : tree' B :=
    match m with
    | Node001 r => Node001 (map' r (xI i))
    | Node010 x => Node010 (f_pos_sym (prev i) x)
    | Node011 x r => Node011 (f_pos_sym (prev i) x) (map' r (xI i))
    | Node100 l => Node100 (map' l (xO i))
    | Node101 l r => Node101 (map' l (xO i)) (map' r (xI i))
    | Node110 l x => Node110 (map' l (xO i)) (f_pos_sym (prev i) x)
    | Node111 l x r => Node111 (map' l (xO i)) (f_pos_sym (prev i) x) (map' r (xI i))
    end.

  Definition map (m: tree A) :=
    match m with
    | Empty => Empty
    | Nodes m => Nodes (map' m xH)
    end.

  Fixpoint map1' (m: tree' A) {struct m} : tree' B :=
    match m with
    | Node001 r => Node001 (map1' r)
    | Node010 x => Node010 (f_sym x)
    | Node011 x r => Node011 (f_sym x) (map1' r)
    | Node100 l => Node100 (map1' l)
    | Node101 l r => Node101 (map1' l) (map1' r)
    | Node110 l x => Node110 (map1' l) (f_sym x)
    | Node111 l x r => Node111 (map1' l) (f_sym x) (map1' r)
    end.

  Definition map1 (m: tree A) : tree B :=
    match m with
    | Empty => Empty
    | Nodes m => Nodes (map1' m)
    end.

  Definition option_map o := 
    match o with 
    | None => None
    | Some a => Some (f_sym a)
    end.

  Fixpoint xelements' (m : tree' A) (i: positive) (k: list (positive * A)) {struct m} : list (positive * A) :=
    match m with
    | Node001 r => xelements' r (xI i) k
    | Node010 x => (prev i, x) :: k
    | Node011 x r => (prev i, x) :: xelements' r (xI i) k
    | Node100 l => xelements' l (xO i) k
    | Node101 l r => xelements' l (xO i) (xelements' r (xI i) k)
    | Node110 l x => xelements' l (xO i) ((prev i, x)::k)
    | Node111 l x r => xelements' l (xO i) ((prev i, x):: (xelements' r (xI i) k))
    end.

  Definition elements (m : tree A) : list (positive * A) := 
    match m with 
    | Empty => nil 
    | Nodes m' => xelements' m' xH nil 
    end.

  Definition xelements (m : tree A) (i: positive) : list (positive * A) := 
    match m with 
    | Empty => nil 
    | Nodes m' => xelements' m' i nil 
    end.

  Definition o2l i o : list (positive * A) := 
    match o with 
    | None => nil
    | Some v => (prev i, v) :: nil
    end.

  Definition o2l_pos i (o : option A) : list (positive) := 
    match o with 
    | None => nil
    | Some _ => prev i :: nil
    end.

  Definition fst_pos_A (x: positive * A) := 
    match x with 
    | (x, _) => x
    end.
  Definition snd_pos_A (x: positive * A) := 
    match x with 
    | (_, x) => x
    end.

  Fixpoint map_fst (xs: list (positive * A)) : list positive := 
    match xs with 
    | nil => nil
    | x :: xs' => fst_pos_A x :: map_fst xs'
    end.

  Definition xkeys (m: tree A) (i: positive) := 
    map_fst (xelements m i).

  Fixpoint In_pos_A (a : (positive * A)) l {struct l} : Prop := 
    match l with
    | [] => False
    | b :: m => b = a \/ In_pos_A a m
    end.

  Fixpoint In_pos (a : positive) l {struct l} : Prop := 
    match l with
    | [] => False
    | b :: m => b = a \/ In_pos a m
    end.

  Fixpoint In_A (a : A) l {struct l} : Prop := 
    match l with
    | [] => False
    | b :: m => b = a \/ In_A a m
    end.

  Fixpoint NoDup_pos_A (l: list (positive * A)) {struct l} : Prop := 
    match l with
    | [] => True
    | b :: m => ~ In_pos_A b m /\ NoDup_pos_A m
    end.

  Fixpoint NoDup_A (l: list A) {struct l} : Prop := 
    match l with
    | [] => True
    | b :: m => ~ In_A b m /\ NoDup_A m
    end.

  Fixpoint NoDup_pos (l: list positive) {struct l} : Prop := 
    match l with
    | [] => True
    | b :: m => ~ In_pos b m /\ NoDup_pos m
    end.

  Definition app_pos_A := Eval compute in @List.app (positive * A).
  Definition app_pos := Eval compute in @List.app positive.
  Definition app_A := Eval compute in @List.app A.

  Variable (f_B_pos_A: B -> positive -> A -> B).
  Definition f_B_pos_A_sym := f_B_pos_A.

  Fixpoint fold' (i: positive) (m: tree' A) (v: B) {struct m} : B :=
    match m with
    | Node001 r => fold' (xI i) r v
    | Node010 x => f_B_pos_A_sym v (prev i) x
    | Node011 x r => fold' (xI i) r (f_B_pos_A_sym v (prev i) x)
    | Node100 l => fold' (xO i) l v
    | Node101 l r => fold' (xI i) r (fold' (xO i) l v)
    | Node110 l x => f_B_pos_A_sym (fold' (xO i) l v) (prev i) x
    | Node111 l x r => fold' (xI i) r (f_B_pos_A_sym (fold' (xO i) l v) (prev i) x)
    end.

  Definition fold (m: tree A) (v: B) :=
    match m with 
    | Empty => v 
    | Nodes m' => fold' xH m' v 
    end.

  Fixpoint list_pos_A_fold_left (xs: list (positive * A)) (acc: B) := 
    match xs with 
    | nil => acc
    | x :: xs' => 
      list_pos_A_fold_left xs' (f_B_pos_A_sym acc (fst_pos_A x) (snd_pos_A x))
    end.

  Variable (f_B_A_B : B -> A -> B).
  Definition f_B_A_B_sym := f_B_A_B.

  Fixpoint fold1' (m: tree' A) (v: B) {struct m} : B :=
    match m with
    | Node001 r => fold1' r v
    | Node010 x => f_B_A_B_sym v x
    | Node011 x r => fold1' r (f_B_A_B_sym v x)
    | Node100 l => fold1' l v
    | Node101 l r => fold1' r (fold1' l v)
    | Node110 l x => f_B_A_B_sym (fold1' l v) x
    | Node111 l x r => fold1' r (f_B_A_B_sym (fold1' l v) x)
    end.

  Definition fold1 (m: tree A) (v: B) : B :=
    match m with 
    | Empty => v 
    | Nodes m' => fold1' m' v 
    end.

  Fixpoint list_A_fold_left (xs: list (positive * A)) (acc: B) := 
    match xs with 
    | nil => acc
    | x :: xs' => 
      list_A_fold_left xs' (f_B_A_B_sym acc (snd_pos_A x))
    end.

  Definition length_pos_A := Eval compute in @List.length (positive * A).
  Definition cardinal (x: tree A) : nat := length_pos_A (elements x).

  Variable (f_pos_A_bool : positive -> A -> bool).
  Definition f_pos_A_bool_sym := f_pos_A_bool.


  Fixpoint fold'_and (i: positive) (m: tree' A) {struct m} : bool :=
    match m with
    | Node001 r => fold'_and (xI i) r
    | Node010 x => f_pos_A_bool_sym (prev i) x
    | Node011 x r => (f_pos_A_bool_sym (prev i) x) && (fold'_and (xI i) r)
    | Node100 l => fold'_and (xO i) l
    | Node101 l r => (fold'_and (xI i) r) && (fold'_and (xO i) l)
    | Node110 l x => ((f_pos_A_bool_sym (prev i) x) && (fold'_and (xO i) l))%bool
    | Node111 l x r => (f_pos_A_bool_sym (prev i) x && (fold'_and (xI i) r) && (fold'_and (xO i) l))
    end.

  Definition fold_and (m: tree A) v :=
    match m with 
    | Empty => v 
    | Nodes m' => (v && fold'_and xH m')%bool
    end.

  Fixpoint fold'_or (i: positive) (m: tree' A) {struct m} : bool :=
    match m with
    | Node001 r => fold'_or (xI i) r
    | Node010 x => f_pos_A_bool_sym (prev i) x
    | Node011 x r => (f_pos_A_bool_sym (prev i) x) && (fold'_or (xI i) r)
    | Node100 l => fold'_or (xO i) l
    | Node101 l r => (fold'_or (xI i) r) && (fold'_or (xO i) l)
    | Node110 l x => ((f_pos_A_bool_sym (prev i) x) && (fold'_or (xO i) l))%bool
    | Node111 l x r => (f_pos_A_bool_sym (prev i) x && (fold'_or (xI i) r) && (fold'_or (xO i) l))
    end.

  Definition fold_or (m: tree A) v :=
    match m with 
    | Empty => v 
    | Nodes m' => (v || fold'_or xH m')%bool
    end.

  Fixpoint fold'_and_neg (i: positive) (m: tree' A) {struct m} : bool :=
    match m with
    | Node001 r => fold'_and_neg (xI i) r
    | Node010 x => negb (f_pos_A_bool_sym (prev i) x)
    | Node011 x r => (negb (f_pos_A_bool_sym (prev i) x)) && (fold'_and_neg (xI i) r)
    | Node100 l => fold'_and_neg (xO i) l
    | Node101 l r => (fold'_and_neg (xI i) r) && (fold'_and_neg (xO i) l)
    | Node110 l x => ((negb (f_pos_A_bool_sym (prev i) x)) && (fold'_and_neg (xO i) l))%bool
    | Node111 l x r => (negb (f_pos_A_bool_sym (prev i) x) && (fold'_and_neg (xI i) r) && (fold'_and_neg (xO i) l))
    end.

  Definition fold_and_neg (m: tree A) v :=
    match m with 
    | Empty => v 
    | Nodes m' => (v && fold'_and_neg xH m')%bool
    end.

  Fixpoint fold'_or_neg (i: positive) (m: tree' A) {struct m} : bool :=
    match m with
    | Node001 r => fold'_or_neg (xI i) r
    | Node010 x => negb (f_pos_A_bool_sym (prev i) x)
    | Node011 x r => (negb (f_pos_A_bool_sym (prev i) x)) && (fold'_or_neg (xI i) r)
    | Node100 l => fold'_or_neg (xO i) l
    | Node101 l r => (fold'_or_neg (xI i) r) && (fold'_or_neg (xO i) l)
    | Node110 l x => ((negb (f_pos_A_bool_sym (prev i) x)) && (fold'_or_neg (xO i) l))%bool
    | Node111 l x r => (negb (f_pos_A_bool_sym (prev i) x) && (fold'_or_neg (xI i) r) && (fold'_or_neg (xO i) l))
    end.

  Definition fold_or_neg (m: tree A) v :=
    match m with 
    | Empty => v 
    | Nodes m' => (v || fold'_or_neg xH m')%bool
    end.

  Definition for_all (m: tree A) : bool :=
    fold_and m true.

  Definition exists_ (m: tree A) : bool :=
    fold_or m false.

  Local Declare ML Module "mirrorsolve".

  From MetaCoq.Template Require Import All Loader.
  Import MCMonadNotation.
  Require Import MirrorSolve.Config.
  Open Scope bs.

  (* Unset Universe Polymorphism. *)

  (* MirrorSolve's automation needs this later. *)
  Universe foo.
  MetaCoq Quote Definition typ_term := Type@{foo}.

  Notation pack x := (existT _ _ x).

  Definition fun_syms : list Config.packed := ([
      pack (PTree.tree' A)
    ; pack (PTree.tree A)
    ; pack (PTree.tree B)
    ; pack (PTree.tree' B)
    ; pack PTree.Node
    ; pack PTree.empty
    ; pack PTree.get'
    ; pack PTree.get
    ; pack PTree.set'
    ; pack PTree.set
    ; pack PTree.set0
    ; pack PTree.rem'
    ; pack PTree.remove'
    ; pack PTree.remove
    ; pack (option A)
    ; pack (option B)
    ; pack positive
    ; pack Pos_eqb
    ; pack (@ite (option A))
    ; pack node'
    ; pack tree_case
    ; pack empty'
    ; pack node_rec'
    ; pack tree_rec'
    ; pack tree'_rec'
    ; pack beqA'
    ; pack beq
    ; pack beq'
    ; pack beq_optA
    ; pack andb
    ; pack orb
    ; pack get_pos_default
    ; pack prev
    ; pack prev_append
    ; pack f_sym
    ; pack f_pos_sym
    ; pack map'
    ; pack map
    ; pack map1'
    ; pack map1
    ; pack option_map
    ; pack elements
    ; pack xelements
    ; pack xelements'
    ; pack (list (positive * A))
    ; pack (list positive)
    ; pack app_pos_A
    ; pack app_pos
    ; pack (positive * A)
    ; pack (@fst positive A)
    ; pack (@snd positive A)
    ; pack o2l
    ; pack map_fst
    ; pack xkeys
    ; pack o2l_pos
    ; pack fst_pos_A
    ; pack snd_pos_A
    ; pack app_A
    ; pack f_B_pos_A_sym
    ; pack fold'
    ; pack fold
    ; pack list_pos_A_fold_left
    ; pack fold1'
    ; pack f_B_A_B_sym
    ; pack fold1
    ; pack list_A_fold_left
    ; pack length_pos_A
    ; pack cardinal
    ; pack Nat.add
    ; pack nat
    ; pack f_pos_A_bool_sym
    ; pack fold'_and
    ; pack fold_and
    ; pack fold'_or
    ; pack fold_or
    ; pack fold'_and_neg
    ; pack fold_and_neg
    ; pack fold'_or_neg
    ; pack fold_or_neg
    ; pack for_all
    ; pack exists_
  ])%type.
  Definition rel_syms : list Config.packed := ([ 
      pack not_trivially_empty
    ; pack get_eq_bool
    ; pack In_pos_A
    ; pack In_pos
    ; pack In_A
    ; pack NoDup_pos_A
    ; pack NoDup_A
    ; pack NoDup_pos
    ; pack Coq.Init.Peano.le
    ; pack Coq.Init.Peano.lt
  ])%type.

  Definition prim_syms : list (Config.packed * String.string) := ([
    (pack (@ite (option A)), "ite")
    ; (pack andb, "and")
    ; (pack orb, "or")
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

  Create HintDb eqns_implicit.
  Create HintDb eqns_explicit.
  Create HintDb eqns_small.

  Create HintDb eqns_empty.

  Ltac prep_proof := 
    hints_foreach (fun x => pose proof x) "eqns_small";
    Utils.revert_all;
    unfold "<->" in *.

  Ltac prep_proof_explicit := 
    hints_foreach (fun x => pose proof x) "eqns_explicit";
    Utils.revert_all;
    unfold "<->" in *.

  Scheme Equality for sorts.

  Ltac mirrorsolve_explicit :=
    try now (timeout 60 (prep_proof_explicit;
    quote_reflect sig fm_model sorts_eq_dec match_tacs match_sorts;
    check_goal_unsat)).

  Definition extract := extract_t2fm sig (fun c => @extract_t2tm sig fm_model sorts_eq_dec c match_tacs) (fun c => @extract_t2rel sig fm_model sorts_eq_dec c match_tacs) (i2srt _ match_sorts) sorts_eq_dec.

  Ltac conv_lemma L := 
    set (l := L);
    unfold "<->" in l;
    let H := type of l in 
    clear l;
    quote_term H (fun x => 
      set (v := (@extract (SLNil _) (reindex_vars x)));
      vm_compute in v;
      match goal with 
      | v := Some ?X |- _ => 
        idtac "converted";
        refine (X)
      | v := None |- _ => 
        idtac "couldn't convert";
        fail
      end
    ).

  Ltac runner := (
    prep_proof;
    quote_reflect sig fm_model sorts_eq_dec match_tacs match_sorts;
    eapply interp_hyps_sound;
    let g := fresh "G" in 
    match goal with 
    | |- interp_wh {| hyps := _ ; p := ?P |} => 
      set (g := P) at 1
    end;
    idtac "starting";
    time "building query" (hints_foreach (fun x => 
      try (unfold "<->" in x);
      let H := type of x in
      quote_term H (fun y => 
      let v := fresh "v" in 
      set (v := (@extract (SLNil _) (reindex_vars y)));
      vm_compute in v;
      match goal with 
      | v' := Some ?X |- interp_wh {| hyps := ?L; p := _ |} => 
        let h := fresh "hyps" in 
        set (h := L) in |- *;
        eapply add_hyp;
        match goal with 
        | |- interp_wh _ => idtac
        | |- _ => 
          eapply denote_extract_specialized_forward with (t := y) (sorts_eq_dec := sorts_eq_dec) (match_tacs := match_tacs) (match_inds := match_sorts);
          [
            match goal with 
            | |- ?T = _ => 
              let t' := fresh "t" in 
              set (t' := T);
              vm_compute in t';
              subst t';
              exact eq_refl
            end
            |
            vm_compute;
            eapply x
          ]
        end;
        clear v
        
      | v' := None |- _ => 
        idtac "couldn't extract??";
        idtac x;
        idtac H;
        idtac y;
        clear v'
      | _ => 
        idtac "unhandled case??";
        idtac y;
        idtac x
      end
      
    )) "eqns_explicit";
    repeat match goal with 
    | x := _ |- _ => 
      subst x
    | H: interp_fm _ _ -> _ |- _ => clear H
    | H: _ = Some _  |- _ => clear H
    | H: denote_t2fm _ _ _ _ _ _ _ _ = _ |- _ => clear H
    end);

    time "query" match goal with 
    | |- ?G => check_unsat_hyps fol_theory G; eapply weaken_hyps; eapply UnsoundAxioms.interp_true
    end
  ).
  Ltac runner_uncheck := (
    prep_proof;
    quote_reflect sig fm_model sorts_eq_dec match_tacs match_sorts;
    eapply interp_hyps_sound;
    let g := fresh "G" in 
    match goal with 
    | |- interp_wh {| hyps := _ ; p := ?P |} => 
      set (g := P) at 1
    end;
    idtac "starting";
    time "building query" (hints_foreach (fun x => 
      try (unfold "<->" in x);
      let H := type of x in
      quote_term H (fun y => 
      let v := fresh "v" in 
      set (v := (@extract (SLNil _) (reindex_vars y)));
      vm_compute in v;
      match goal with 
      | v' := Some ?X |- interp_wh {| hyps := ?L; p := _ |} => 
        let h := fresh "hyps" in 
        set (h := L) in |- *;
        eapply add_hyp;
        match goal with 
        | |- interp_wh _ => idtac
        | |- _ => 
          eapply UnsoundAxioms.interp_true with (m := fm_model) (form := X)
        end;
        clear v
        
      | v' := None |- _ => 
        (* idtac "couldn't extract??";
        idtac x;
        idtac H;
        idtac y;
        clear v' *)
        idtac
      end
      
    )) "eqns_explicit";
    repeat match goal with 
    | x := _ |- _ => 
      subst x
    | H: interp_fm _ _ -> _ |- _ => clear H
    | H: _ = Some _  |- _ => clear H
    | H: denote_t2fm _ _ _ _ _ _ _ _ = _ |- _ => clear H
    end);

    time "query" match goal with 
    | |- ?G => check_unsat_hyps fol_theory G; eapply weaken_hyps; eapply UnsoundAxioms.interp_true
    end
  ).
  Ltac runner_uncheck_opt := 
    prep_proof;
    quote_reflect sig fm_model sorts_eq_dec match_tacs match_sorts;

    time "query" match goal with 
    | |- ?G => check_unsat_opt "eqns_implicit" fol_theory G; eapply UnsoundAxioms.interp_true
    end.
  Ltac mirrorsolve_full := try now ( timeout 60 runner).
  Ltac mirrorsolve_uncheck := try now ( timeout 60 runner_uncheck).
  Ltac mirrorsolve := try now ( timeout 60 runner_uncheck_opt).

  Definition denote := denote_t2fm sig fm_model sorts_eq_dec (denote_tm _ fm_model sorts_eq_dec match_tacs) (denote_t2rel _ fm_model sorts_eq_dec match_tacs) (i2srt _ match_sorts) (VEmp _ _).

(** ** Good variable properties for the basic operations *)

  (* MirrorSolve hints *)
  Hint Immediate get'_equation_1 : eqns_small.
  Hint Immediate get'_equation_1 : eqns_explicit.
  Hint Immediate get'_equation_2 : eqns_explicit.
  Hint Immediate get'_equation_2 : eqns_explicit.
  Hint Immediate get'_equation_3 : eqns_explicit.
  Hint Immediate get'_equation_4 : eqns_explicit.
  Hint Immediate get'_equation_5 : eqns_explicit.
  Hint Immediate get'_equation_6 : eqns_explicit.
  Hint Immediate get'_equation_7 : eqns_explicit.
  Hint Immediate get'_equation_8 : eqns_explicit.
  Hint Immediate get'_equation_9 : eqns_explicit.
  Hint Immediate get'_equation_10 : eqns_explicit.
  Hint Immediate get'_equation_11 : eqns_explicit.
  Hint Immediate get'_equation_12 : eqns_explicit.
  Hint Immediate get'_equation_13 : eqns_explicit.
  Hint Immediate get'_equation_14 : eqns_explicit.
  Hint Immediate get'_equation_15 : eqns_explicit.
  Hint Immediate get'_equation_16 : eqns_explicit.
  Hint Immediate get'_equation_17 : eqns_explicit.
  Hint Immediate get'_equation_18 : eqns_explicit.
  Hint Immediate get'_equation_19 : eqns_explicit.
  Hint Immediate get'_equation_20 : eqns_explicit.
  Hint Immediate get'_equation_21 : eqns_explicit.

  Hint Immediate tree_case_equation_1 : eqns_small.
  Hint Immediate tree_case_equation_1 : eqns_explicit.
  Hint Immediate tree_case_equation_2 : eqns_explicit.
  Hint Immediate tree_case_equation_3 : eqns_explicit.
  Hint Immediate tree_case_equation_4 : eqns_explicit.
  Hint Immediate tree_case_equation_5 : eqns_explicit.
  Hint Immediate tree_case_equation_6 : eqns_explicit.
  Hint Immediate tree_case_equation_7 : eqns_explicit.
  Hint Immediate tree_case_equation_8 : eqns_explicit.

  Hint Immediate tree'_rec'_equation_1 : eqns_small.
  Hint Immediate tree'_rec'_equation_1 : eqns_explicit.
  Hint Immediate tree'_rec'_equation_2 : eqns_explicit.
  Hint Immediate tree'_rec'_equation_3 : eqns_explicit.
  Hint Immediate tree'_rec'_equation_4 : eqns_explicit.
  Hint Immediate tree'_rec'_equation_5 : eqns_explicit.
  Hint Immediate tree'_rec'_equation_6 : eqns_explicit.
  Hint Immediate tree'_rec'_equation_7 : eqns_explicit.

  Hint Immediate get_equation_1 : eqns_small.
  Hint Immediate get_equation_1 : eqns_explicit.
  Hint Immediate get_equation_2 : eqns_explicit.

  Hint Immediate empty_equation_1 : eqns_small.
  Hint Immediate empty_equation_1 : eqns_explicit.

  Hint Immediate beq'_equation_1 : eqns_small.
  Hint Immediate beq'_equation_1 : eqns_explicit.
  Hint Immediate beq'_equation_2 : eqns_explicit.
  Hint Immediate beq'_equation_3 : eqns_explicit.
  Hint Immediate beq'_equation_4 : eqns_explicit.
  Hint Immediate beq'_equation_5 : eqns_explicit.
  Hint Immediate beq'_equation_6 : eqns_explicit.
  Hint Immediate beq'_equation_7 : eqns_explicit.
  Hint Immediate beq'_equation_8 : eqns_explicit.
  Hint Immediate beq'_equation_9 : eqns_explicit. 
  Hint Immediate beq'_equation_10 : eqns_explicit.
  
  Hint Immediate beq'_equation_11 : eqns_explicit.
  Hint Immediate beq'_equation_12 : eqns_explicit.
  Hint Immediate beq'_equation_13 : eqns_explicit.
  Hint Immediate beq'_equation_14 : eqns_explicit.
  Hint Immediate beq'_equation_15 : eqns_explicit.
  Hint Immediate beq'_equation_16 : eqns_explicit.
  Hint Immediate beq'_equation_17 : eqns_explicit.
  Hint Immediate beq'_equation_18 : eqns_explicit.
  Hint Immediate beq'_equation_19 : eqns_explicit.
  Hint Immediate beq'_equation_20 : eqns_explicit.
  Hint Immediate beq'_equation_21 : eqns_explicit.
  Hint Immediate beq'_equation_22 : eqns_explicit.
  Hint Immediate beq'_equation_23 : eqns_explicit.
  Hint Immediate beq'_equation_24 : eqns_explicit.
  Hint Immediate beq'_equation_25 : eqns_explicit.
  Hint Immediate beq'_equation_26 : eqns_explicit.
  Hint Immediate beq'_equation_27 : eqns_explicit.
  Hint Immediate beq'_equation_28 : eqns_explicit.
  Hint Immediate beq'_equation_29 : eqns_explicit.
  Hint Immediate beq'_equation_30 : eqns_explicit.
  Hint Immediate beq'_equation_31 : eqns_explicit.
  Hint Immediate beq'_equation_32 : eqns_explicit.
  Hint Immediate beq'_equation_33 : eqns_explicit.
  Hint Immediate beq'_equation_34 : eqns_explicit.
  Hint Immediate beq'_equation_35 : eqns_explicit.
  Hint Immediate beq'_equation_36 : eqns_explicit.
  Hint Immediate beq'_equation_37 : eqns_explicit.
  Hint Immediate beq'_equation_38 : eqns_explicit.
  Hint Immediate beq'_equation_39 : eqns_explicit.
  Hint Immediate beq'_equation_40 : eqns_explicit.
  Hint Immediate beq'_equation_41 : eqns_explicit.
  Hint Immediate beq'_equation_42 : eqns_explicit.
  Hint Immediate beq'_equation_43 : eqns_explicit.
  Hint Immediate beq'_equation_44 : eqns_explicit.
  Hint Immediate beq'_equation_45 : eqns_explicit.
  Hint Immediate beq'_equation_46 : eqns_explicit.
  Hint Immediate beq'_equation_47 : eqns_explicit.
  Hint Immediate beq'_equation_48 : eqns_explicit. 
  Hint Immediate beq'_equation_49 : eqns_explicit.

  Hint Immediate beq_equation_1 : eqns_small.
  Hint Immediate beq_equation_1 : eqns_explicit.
  Hint Immediate beq_equation_2 : eqns_explicit.
  Hint Immediate beq_equation_3 : eqns_explicit.
  Hint Immediate beq_equation_4 : eqns_explicit. 

  Hint Immediate beq_optA_equation_1 : eqns_small.
  Hint Immediate beq_optA_equation_1 : eqns_explicit.
  Hint Immediate beq_optA_equation_2 : eqns_explicit.
  Hint Immediate beq_optA_equation_3 : eqns_explicit.
  Hint Immediate beq_optA_equation_4 : eqns_explicit. 

  MetaCoq Run (infer_equations map).
  Hint Immediate map_equation_1 : eqns_small.
  Hint Immediate map_equation_1 : eqns_explicit.
  Hint Immediate map_equation_2 : eqns_explicit.

  MetaCoq Run (infer_equations map').
  Hint Immediate map'_equation_1 : eqns_small.
  Hint Immediate map'_equation_1 : eqns_explicit.
  Hint Immediate map'_equation_2 : eqns_explicit.
  Hint Immediate map'_equation_3 : eqns_explicit.
  Hint Immediate map'_equation_4 : eqns_explicit.
  Hint Immediate map'_equation_5 : eqns_explicit.
  Hint Immediate map'_equation_6 : eqns_explicit.
  Hint Immediate map'_equation_7 : eqns_explicit.

  MetaCoq Run (infer_equations map1).
  Hint Immediate map1_equation_1 : eqns_small.
  Hint Immediate map1_equation_1 : eqns_explicit.
  Hint Immediate map1_equation_2 : eqns_explicit.

  MetaCoq Run (infer_equations map1').
  Hint Immediate map1'_equation_1 : eqns_small.
  Hint Immediate map1'_equation_1 : eqns_explicit.
  Hint Immediate map1'_equation_2 : eqns_explicit.
  Hint Immediate map1'_equation_3 : eqns_explicit.
  Hint Immediate map1'_equation_4 : eqns_explicit.
  Hint Immediate map1'_equation_5 : eqns_explicit.
  Hint Immediate map1'_equation_6 : eqns_explicit.
  Hint Immediate map1'_equation_7 : eqns_explicit.

  MetaCoq Run (infer_equations fold').
  Hint Immediate fold'_equation_1 : eqns_small.
  Hint Immediate fold'_equation_1 : eqns_explicit.
  Hint Immediate fold'_equation_2 : eqns_explicit.
  Hint Immediate fold'_equation_3 : eqns_explicit.
  Hint Immediate fold'_equation_4 : eqns_explicit.
  Hint Immediate fold'_equation_5 : eqns_explicit.
  Hint Immediate fold'_equation_6 : eqns_explicit.
  Hint Immediate fold'_equation_7 : eqns_explicit.

  MetaCoq Run (infer_equations fold1').
  Hint Immediate fold1'_equation_1 : eqns_small.
  Hint Immediate fold1'_equation_1 : eqns_explicit.
  Hint Immediate fold1'_equation_2 : eqns_explicit.
  Hint Immediate fold1'_equation_3 : eqns_explicit.
  Hint Immediate fold1'_equation_4 : eqns_explicit.
  Hint Immediate fold1'_equation_5 : eqns_explicit.
  Hint Immediate fold1'_equation_6 : eqns_explicit.
  Hint Immediate fold1'_equation_7 : eqns_explicit.

  MetaCoq Run (infer_equations fold'_and).
  Hint Immediate fold'_and_equation_1 : eqns_small.
  Hint Immediate fold'_and_equation_1 : eqns_explicit.
  Hint Immediate fold'_and_equation_2 : eqns_explicit.
  Hint Immediate fold'_and_equation_3 : eqns_explicit.
  Hint Immediate fold'_and_equation_4 : eqns_explicit.
  Hint Immediate fold'_and_equation_5 : eqns_explicit.
  Hint Immediate fold'_and_equation_6 : eqns_explicit.
  Hint Immediate fold'_and_equation_7 : eqns_explicit.

  (* crush hints *)
  Hint Resolve get'_equation_1.
  Hint Resolve get'_equation_2.
  Hint Resolve get'_equation_3.
  Hint Resolve get'_equation_4.
  Hint Resolve get'_equation_5.
  Hint Resolve get'_equation_6.
  Hint Resolve get'_equation_7.
  Hint Resolve get'_equation_8.
  Hint Resolve get'_equation_9.
  Hint Resolve get'_equation_10.
  Hint Resolve get'_equation_11.
  Hint Resolve get'_equation_12.
  Hint Resolve get'_equation_13.
  Hint Resolve get'_equation_14.
  Hint Resolve get'_equation_15.
  Hint Resolve get'_equation_16.
  Hint Resolve get'_equation_17.
  Hint Resolve get'_equation_18.
  Hint Resolve get'_equation_19.
  Hint Resolve get'_equation_20.
  Hint Resolve get'_equation_21.

  Hint Resolve tree_case_equation_1.
  Hint Resolve tree_case_equation_2.
  Hint Resolve tree_case_equation_3.
  Hint Resolve tree_case_equation_4.
  Hint Resolve tree_case_equation_5.
  Hint Resolve tree_case_equation_6.
  Hint Resolve tree_case_equation_7.
  Hint Resolve tree_case_equation_8.

  Hint Resolve tree'_rec'_equation_1.
  Hint Resolve tree'_rec'_equation_2.
  Hint Resolve tree'_rec'_equation_3.
  Hint Resolve tree'_rec'_equation_4.
  Hint Resolve tree'_rec'_equation_5.
  Hint Resolve tree'_rec'_equation_6.
  Hint Resolve tree'_rec'_equation_7.

  Hint Resolve get_equation_1.
  Hint Resolve get_equation_2.

  Hint Resolve empty_equation_1.

  Hint Resolve beq'_equation_1.
  Hint Resolve beq'_equation_2.
  Hint Resolve beq'_equation_3.
  Hint Resolve beq'_equation_4.
  Hint Resolve beq'_equation_5.
  Hint Resolve beq'_equation_6.
  Hint Resolve beq'_equation_7.
  Hint Resolve beq'_equation_8.
  Hint Resolve beq'_equation_9.
  Hint Resolve beq'_equation_10.
  
  Hint Resolve beq'_equation_11.
  Hint Resolve beq'_equation_12.
  Hint Resolve beq'_equation_13.
  Hint Resolve beq'_equation_14.
  Hint Resolve beq'_equation_15.
  Hint Resolve beq'_equation_16.
  Hint Resolve beq'_equation_17.
  Hint Resolve beq'_equation_18.
  Hint Resolve beq'_equation_19.
  Hint Resolve beq'_equation_20.
  Hint Resolve beq'_equation_21.
  Hint Resolve beq'_equation_22.
  Hint Resolve beq'_equation_23.
  Hint Resolve beq'_equation_24.
  Hint Resolve beq'_equation_25.
  Hint Resolve beq'_equation_26.
  Hint Resolve beq'_equation_27.
  Hint Resolve beq'_equation_28.
  Hint Resolve beq'_equation_29.
  Hint Resolve beq'_equation_30.
  Hint Resolve beq'_equation_31.
  Hint Resolve beq'_equation_32.
  Hint Resolve beq'_equation_33.
  Hint Resolve beq'_equation_34.
  Hint Resolve beq'_equation_35.
  Hint Resolve beq'_equation_36.
  Hint Resolve beq'_equation_37.
  Hint Resolve beq'_equation_38.
  Hint Resolve beq'_equation_39.
  Hint Resolve beq'_equation_40.
  Hint Resolve beq'_equation_41.
  Hint Resolve beq'_equation_42.
  Hint Resolve beq'_equation_43.
  Hint Resolve beq'_equation_44.
  Hint Resolve beq'_equation_45.
  Hint Resolve beq'_equation_46.
  Hint Resolve beq'_equation_47.
  Hint Resolve beq'_equation_48.
  Hint Resolve beq'_equation_49.

  Hint Resolve beq_equation_1.
  Hint Resolve beq_equation_2.
  Hint Resolve beq_equation_3.
  Hint Resolve beq_equation_4.

  Hint Resolve beq_optA_equation_1.
  Hint Resolve beq_optA_equation_2.
  Hint Resolve beq_optA_equation_3.
  Hint Resolve beq_optA_equation_4.

  Hint Resolve map1'_equation_1.
  Hint Resolve map1'_equation_1.
  Hint Resolve map1'_equation_2.
  Hint Resolve map1'_equation_3.
  Hint Resolve map1'_equation_4.
  Hint Resolve map1'_equation_5.
  Hint Resolve map1'_equation_6.
  Hint Resolve map1'_equation_7.

  Hint Resolve map1_equation_1.
  Hint Resolve map1_equation_1.
  Hint Resolve map1_equation_2.

  Hint Resolve map'_equation_1.
  Hint Resolve map'_equation_1.
  Hint Resolve map'_equation_2.
  Hint Resolve map'_equation_3.
  Hint Resolve map'_equation_4.
  Hint Resolve map'_equation_5.
  Hint Resolve map'_equation_6.
  Hint Resolve map'_equation_7.

  Hint Resolve fold1'_equation_1.
  Hint Resolve fold1'_equation_2.
  Hint Resolve fold1'_equation_3.
  Hint Resolve fold1'_equation_4.
  Hint Resolve fold1'_equation_5.
  Hint Resolve fold1'_equation_6.
  Hint Resolve fold1'_equation_7.

  Hint Resolve fold'_equation_1.
  Hint Resolve fold'_equation_2.
  Hint Resolve fold'_equation_3.
  Hint Resolve fold'_equation_4.
  Hint Resolve fold'_equation_5.
  Hint Resolve fold'_equation_6.
  Hint Resolve fold'_equation_7.

  (* optimized equations *)

  Definition get'_equation_1_P  : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac: ( set (v := ltac:(conv_lemma get'_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v) ).
  Hint Immediate get'_equation_1_P  : eqns_implicit.
  Hint Immediate (get'_equation_1_P ) : eqns_implicit.
  Definition get'_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_2_P : eqns_implicit.
  Definition get'_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_3_P : eqns_implicit.
  Definition get'_equation_4_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_4)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_4_P : eqns_implicit.
  Definition get'_equation_5_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_5)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_5_P : eqns_implicit.
  Definition get'_equation_6_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_6)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_6_P : eqns_implicit.
  Definition get'_equation_7_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_7)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_7_P : eqns_implicit.
  Definition get'_equation_8_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_8)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_8_P : eqns_implicit.
  Definition get'_equation_9_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_9)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_9_P : eqns_implicit.
  Definition get'_equation_10_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_10)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_10_P : eqns_implicit.
  Definition get'_equation_11_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_11)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_11_P : eqns_implicit.
  Definition get'_equation_12_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_12)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_12_P : eqns_implicit.
  Definition get'_equation_13_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_13)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_13_P : eqns_implicit.
  Definition get'_equation_14_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_14)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_14_P : eqns_implicit.
  Definition get'_equation_15_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_15)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_15_P : eqns_implicit.
  Definition get'_equation_16_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_16)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_16_P : eqns_implicit.
  Definition get'_equation_17_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_17)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_17_P : eqns_implicit.
  Definition get'_equation_18_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_18)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_18_P : eqns_implicit.
  Definition get'_equation_19_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_19)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_19_P : eqns_implicit.
  Definition get'_equation_20_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_20)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_20_P : eqns_implicit.
  Definition get'_equation_21_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get'_equation_21)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get'_equation_21_P : eqns_implicit.

  Definition tree_case_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma tree_case_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate tree_case_equation_1_P : eqns_implicit.
  Definition tree_case_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma tree_case_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate tree_case_equation_2_P : eqns_implicit.
  Definition tree_case_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma tree_case_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate tree_case_equation_3_P : eqns_implicit.
  Definition tree_case_equation_4_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma tree_case_equation_4)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate tree_case_equation_4_P : eqns_implicit.
  Definition tree_case_equation_5_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma tree_case_equation_5)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate tree_case_equation_5_P : eqns_implicit.
  Definition tree_case_equation_6_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma tree_case_equation_6)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate tree_case_equation_6_P : eqns_implicit.
  Definition tree_case_equation_7_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma tree_case_equation_7)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate tree_case_equation_7_P : eqns_implicit.
  Definition tree_case_equation_8_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma tree_case_equation_8)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate tree_case_equation_8_P : eqns_implicit.

  Definition tree'_rec'_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma tree'_rec'_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate tree'_rec'_equation_1_P : eqns_implicit.
  Definition tree'_rec'_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma tree'_rec'_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate tree'_rec'_equation_2_P : eqns_implicit.
  Definition tree'_rec'_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma tree'_rec'_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate tree'_rec'_equation_3_P : eqns_implicit.
  Definition tree'_rec'_equation_4_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma tree'_rec'_equation_4)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate tree'_rec'_equation_4_P : eqns_implicit.
  Definition tree'_rec'_equation_5_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma tree'_rec'_equation_5)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate tree'_rec'_equation_5_P : eqns_implicit.
  Definition tree'_rec'_equation_6_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma tree'_rec'_equation_6)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate tree'_rec'_equation_6_P : eqns_implicit.
  Definition tree'_rec'_equation_7_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma tree'_rec'_equation_7)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate tree'_rec'_equation_7_P : eqns_implicit.

  Definition get_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get_equation_1_P : eqns_implicit.
  Definition get_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get_equation_2_P : eqns_implicit.

  Definition empty_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma empty_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate empty_equation_1_P : eqns_implicit.

  Definition beq'_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_1_P : eqns_implicit.
  Definition beq'_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_2_P : eqns_implicit.
  Definition beq'_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_3_P : eqns_implicit.
  Definition beq'_equation_4_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_4)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_4_P : eqns_implicit.
  Definition beq'_equation_5_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_5)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_5_P : eqns_implicit.
  Definition beq'_equation_6_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_6)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_6_P : eqns_implicit.
  Definition beq'_equation_7_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_7)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_7_P : eqns_implicit.
  Definition beq'_equation_8_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_8)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_8_P : eqns_implicit.
  Definition beq'_equation_9_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_9)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_9_P : eqns_implicit.
  Definition beq'_equation_10_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_10)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_10_P : eqns_implicit.
  
  Definition beq'_equation_11_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_11)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_11_P : eqns_implicit.
  Definition beq'_equation_12_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_12)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_12_P : eqns_implicit.
  Definition beq'_equation_13_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_13)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_13_P : eqns_implicit.
  Definition beq'_equation_14_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_14)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_14_P : eqns_implicit.
  Definition beq'_equation_15_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_15)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_15_P : eqns_implicit.
  Definition beq'_equation_16_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_16)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_16_P : eqns_implicit.
  Definition beq'_equation_17_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_17)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_17_P : eqns_implicit.
  Definition beq'_equation_18_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_18)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_18_P : eqns_implicit.
  Definition beq'_equation_19_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_19)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_19_P : eqns_implicit.
  Definition beq'_equation_20_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_20)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_20_P : eqns_implicit.
  Definition beq'_equation_21_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_21)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_21_P : eqns_implicit.
  Definition beq'_equation_22_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_22)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_22_P : eqns_implicit.
  Definition beq'_equation_23_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_23)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_23_P : eqns_implicit.
  Definition beq'_equation_24_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_24)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_24_P : eqns_implicit.
  Definition beq'_equation_25_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_25)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_25_P : eqns_implicit.
  Definition beq'_equation_26_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_26)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_26_P : eqns_implicit.
  Definition beq'_equation_27_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_27)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_27_P : eqns_implicit.
  Definition beq'_equation_28_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_28)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_28_P : eqns_implicit.
  Definition beq'_equation_29_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_29)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_29_P : eqns_implicit.
  Definition beq'_equation_30_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_30)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_30_P : eqns_implicit.
  Definition beq'_equation_31_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_31)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_31_P : eqns_implicit.
  Definition beq'_equation_32_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_32)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_32_P : eqns_implicit.
  Definition beq'_equation_33_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_33)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_33_P : eqns_implicit.
  Definition beq'_equation_34_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_34)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_34_P : eqns_implicit.
  Definition beq'_equation_35_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_35)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_35_P : eqns_implicit.
  Definition beq'_equation_36_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_36)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_36_P : eqns_implicit.
  Definition beq'_equation_37_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_37)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_37_P : eqns_implicit.
  Definition beq'_equation_38_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_38)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_38_P : eqns_implicit.
  Definition beq'_equation_39_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_39)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_39_P : eqns_implicit.
  Definition beq'_equation_40_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_40)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_40_P : eqns_implicit.
  Definition beq'_equation_41_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_41)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_41_P : eqns_implicit.
  Definition beq'_equation_42_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_42)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_42_P : eqns_implicit.
  Definition beq'_equation_43_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_43)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_43_P : eqns_implicit.
  Definition beq'_equation_44_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_44)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_44_P : eqns_implicit.
  Definition beq'_equation_45_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_45)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_45_P : eqns_implicit.
  Definition beq'_equation_46_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_46)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_46_P : eqns_implicit.
  Definition beq'_equation_47_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_47)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_47_P : eqns_implicit.
  Definition beq'_equation_48_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_48)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_48_P : eqns_implicit.
  Definition beq'_equation_49_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_equation_49)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_equation_49_P : eqns_implicit.

  Definition beq_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq_equation_1_P : eqns_implicit.
  Definition beq_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq_equation_2_P : eqns_implicit.
  Definition beq_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq_equation_3_P : eqns_implicit.
  Definition beq_equation_4_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq_equation_4)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq_equation_4_P : eqns_implicit.

  Definition beq_optA_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq_optA_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq_optA_equation_1_P : eqns_implicit.
  Definition beq_optA_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq_optA_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq_optA_equation_2_P : eqns_implicit.
  Definition beq_optA_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq_optA_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq_optA_equation_3_P : eqns_implicit.
  Definition beq_optA_equation_4_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq_optA_equation_4)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq_optA_equation_4_P : eqns_implicit.

  Definition map1'_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map1'_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map1'_equation_1_P : eqns_implicit.
  Definition map1'_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map1'_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map1'_equation_2_P : eqns_implicit.
  Definition map1'_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map1'_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map1'_equation_3_P : eqns_implicit.
  Definition map1'_equation_4_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map1'_equation_4)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map1'_equation_4_P : eqns_implicit.
  Definition map1'_equation_5_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map1'_equation_5)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map1'_equation_5_P : eqns_implicit.
  Definition map1'_equation_6_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map1'_equation_6)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map1'_equation_6_P : eqns_implicit.
  Definition map1'_equation_7_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map1'_equation_7)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map1'_equation_7_P : eqns_implicit.

  Definition map1_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map1_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map1_equation_1_P : eqns_implicit.
  Definition map1_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map1_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map1_equation_2_P : eqns_implicit.

  Definition map'_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map'_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map'_equation_1_P : eqns_implicit.
  Definition map'_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map'_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map'_equation_2_P : eqns_implicit.
  Definition map'_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map'_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map'_equation_3_P : eqns_implicit.
  Definition map'_equation_4_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map'_equation_4)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map'_equation_4_P : eqns_implicit.
  Definition map'_equation_5_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map'_equation_5)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map'_equation_5_P : eqns_implicit.
  Definition map'_equation_6_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map'_equation_6)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map'_equation_6_P : eqns_implicit.
  Definition map'_equation_7_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map'_equation_7)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map'_equation_7_P : eqns_implicit.

  Definition fold1'_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold1'_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold1'_equation_1_P : eqns_implicit.
  Definition fold1'_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold1'_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold1'_equation_2_P : eqns_implicit.
  Definition fold1'_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold1'_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold1'_equation_3_P : eqns_implicit.
  Definition fold1'_equation_4_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold1'_equation_4)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold1'_equation_4_P : eqns_implicit.
  Definition fold1'_equation_5_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold1'_equation_5)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold1'_equation_5_P : eqns_implicit.
  Definition fold1'_equation_6_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold1'_equation_6)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold1'_equation_6_P : eqns_implicit.
  Definition fold1'_equation_7_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold1'_equation_7)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold1'_equation_7_P : eqns_implicit.
  Definition fold'_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold'_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold'_equation_1_P : eqns_implicit.
  Definition fold'_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold'_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold'_equation_2_P : eqns_implicit.
  Definition fold'_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold'_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold'_equation_3_P : eqns_implicit.
  Definition fold'_equation_4_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold'_equation_4)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold'_equation_4_P : eqns_implicit.
  Definition fold'_equation_5_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold'_equation_5)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold'_equation_5_P : eqns_implicit.
  Definition fold'_equation_6_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold'_equation_6)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold'_equation_6_P : eqns_implicit.
  Definition fold'_equation_7_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold'_equation_7)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold'_equation_7_P : eqns_implicit.


  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 3, "ms": 3, "hammer": 3, "crush": 3} *)
  Theorem gempty:
    forall (i: positive), get i (empty) = None.
  Proof.
    induction i;
    hammer'.
    Restart.
    induction i;
    crush'.
    Restart.
    induction i;
    mirrorsolve.
  Time Qed.

  Hint Immediate gempty : eqns_explicit.
  Hint Resolve gempty.

  Definition gempty_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma gempty)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate gempty_P : eqns_implicit.

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":1, "ms":1, "hammer":1, "crush":1} *)
  Lemma gEmpty:
    forall (i: positive), get i (@Empty A) = None.
  Proof. 
    hammer'.
    Restart.
    crush'.
    Restart.
    mirrorsolve.
  Qed.

  Hint Immediate set0_equation_1 : eqns_explicit.
  Hint Immediate set0_equation_2 : eqns_explicit.
  Hint Immediate set0_equation_3 : eqns_explicit.

  Definition set0_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set0_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set0_equation_1_P : eqns_implicit.

  Definition set0_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set0_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set0_equation_2_P : eqns_implicit.

  Definition set0_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set0_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set0_equation_3_P : eqns_implicit.


  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":3, "ms":3, "hammer":3, "crush":3} *)
  Lemma gss0: forall p (x: A), get' p (set0 p x) = Some x.
  Proof. 
    induction p;
    hammer'.
    Restart.
    induction p;
    crush'.
    Restart.
    induction p;
    mirrorsolve.
  Qed.

  Hint Immediate gss0 : eqns_explicit.
  Hint Resolve gss0.

  Definition gss0_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma gss0)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate gss0_P : eqns_implicit.


  Set MirrorSolve Solver "z3".
  Set MirrorSolve Solver Flags "-T:5".

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":6, "ms":6, "hammer":6, "crush":4} *)
  Lemma gso0: forall p q (x: A), p<>q -> get' p (set0 q x) = None.
  Proof.
    induction p;
    induction q;
    hammer'.
    Restart.
    induction p;
    induction q;
    crush'.
    Restart.
    induction p;
    induction q;
    mirrorsolve.
  Time Qed.

  Hint Immediate gso0 : eqns_explicit.
  Hint Resolve gso0.

  Definition gso0_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma gso0)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate gso0_P : eqns_implicit.

  Hint Immediate set'_equation_1 : eqns_explicit.
  Hint Immediate set'_equation_2 : eqns_explicit.
  Hint Immediate set'_equation_3 : eqns_explicit.
  Hint Immediate set'_equation_4 : eqns_explicit.
  Hint Immediate set'_equation_5 : eqns_explicit.
  Hint Immediate set'_equation_6 : eqns_explicit.
  Hint Immediate set'_equation_7 : eqns_explicit.
  Hint Immediate set'_equation_8 : eqns_explicit.
  Hint Immediate set'_equation_9 : eqns_explicit.
  Hint Immediate set'_equation_10 : eqns_explicit.
  Hint Immediate set'_equation_11 : eqns_explicit.
  Hint Immediate set'_equation_12 : eqns_explicit.
  Hint Immediate set'_equation_13 : eqns_explicit.
  Hint Immediate set'_equation_14 : eqns_explicit.
  Hint Immediate set'_equation_15 : eqns_explicit.
  Hint Immediate set'_equation_16 : eqns_explicit.
  Hint Immediate set'_equation_17 : eqns_explicit.
  Hint Immediate set'_equation_18 : eqns_explicit.
  Hint Immediate set'_equation_19 : eqns_explicit.
  Hint Immediate set'_equation_20 : eqns_explicit.
  Hint Immediate set'_equation_21 : eqns_explicit.

  Hint Immediate set_equation_1 : eqns_explicit.
  Hint Immediate set_equation_2 : eqns_explicit.

  Definition set'_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_1_P : eqns_implicit.
  Definition set'_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_2_P : eqns_implicit.
  Definition set'_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_3_P : eqns_implicit.
  Definition set'_equation_4_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_4)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_4_P : eqns_implicit.
  Definition set'_equation_5_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_5)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_5_P : eqns_implicit.
  Definition set'_equation_6_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_6)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_6_P : eqns_implicit.
  Definition set'_equation_7_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_7)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_7_P : eqns_implicit.
  Definition set'_equation_8_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_8)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_8_P : eqns_implicit.
  Definition set'_equation_9_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_9)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_9_P : eqns_implicit.
  Definition set'_equation_10_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_10)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_10_P : eqns_implicit.
  Definition set'_equation_11_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_11)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_11_P : eqns_implicit.
  Definition set'_equation_12_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_12)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_12_P : eqns_implicit.
  Definition set'_equation_13_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_13)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_13_P : eqns_implicit.
  Definition set'_equation_14_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_14)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_14_P : eqns_implicit.
  Definition set'_equation_15_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_15)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_15_P : eqns_implicit.
  Definition set'_equation_16_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_16)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_16_P : eqns_implicit.
  Definition set'_equation_17_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_17)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_17_P : eqns_implicit.
  Definition set'_equation_18_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_18)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_18_P : eqns_implicit.
  Definition set'_equation_19_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_19)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_19_P : eqns_implicit.
  Definition set'_equation_20_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_20)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_20_P : eqns_implicit.
  Definition set'_equation_21_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set'_equation_21)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set'_equation_21_P : eqns_implicit.
  Definition set_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set_equation_1_P : eqns_implicit.
  Definition set_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set_equation_2_P : eqns_implicit.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":21, "ms":21, "hammer":21, "crush":7} *)
  Lemma gss':
    forall i x m, 
      get' i (set' i x m) = Some x.
  Proof.
    induction i;
    induction m;
    hammer'.
    Restart.
    induction i;
    induction m;
    crush'.
    Restart.
    induction i;
    induction m;
    mirrorsolve.
  Time Qed.

  Hint Immediate gss' : eqns_explicit.
  Hint Resolve gss'.

  Definition gss'_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma gss')); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate gss'_P : eqns_implicit.

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":2, "hammer":2, "crush":1} *)
  Theorem gss:
    forall (i: positive) (x: A) (m: tree A), get i (set i x m) = Some x.
  Proof.
    induction m;
    hammer'.
    Restart.
    induction m;
    crush'.
    Restart.
    induction m;
    mirrorsolve.
  Qed.

  Hint Immediate gss : eqns_explicit.
  Definition gss_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma gss)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate gss_P : eqns_implicit.

  Hint Resolve gss.


  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":63, "ms":63, "hammer":63, "crush":49} *)
  Theorem gso':
    forall (i j: positive) (x: A) (m: tree' A),
    i <> j -> get' i (set' j x m) = get' i m.
  Proof.
    induction i;
    induction j;
    induction m;
    hammer'.
    Restart.
    induction i;
    induction j;
    induction m;
    crush'.
    Restart.

    time (induction i;
    induction j;
    induction m;
    mirrorsolve).
  Time Qed.

  Hint Immediate gso': eqns_explicit.
  Definition gso'_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma gso')); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate gso'_P : eqns_implicit.

  Hint Resolve gso'.

  Hint Immediate Pos_eqb_equation_1 : eqns_explicit.
  Hint Immediate Pos_eqb_equation_2 : eqns_explicit.
  Hint Immediate Pos_eqb_equation_3 : eqns_explicit.
  Hint Immediate Pos_eqb_equation_4 : eqns_explicit.
  Hint Immediate Pos_eqb_equation_5 : eqns_explicit.
  Hint Immediate Pos_eqb_equation_6 : eqns_explicit.
  Hint Immediate Pos_eqb_equation_7 : eqns_explicit.
  Hint Immediate Pos_eqb_equation_8 : eqns_explicit.
  Hint Immediate Pos_eqb_equation_9 : eqns_explicit.

  Definition Pos_eqb_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma Pos_eqb_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate Pos_eqb_equation_1_P : eqns_implicit.
  Definition Pos_eqb_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma Pos_eqb_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate Pos_eqb_equation_2_P : eqns_implicit.
  Definition Pos_eqb_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma Pos_eqb_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate Pos_eqb_equation_3_P : eqns_implicit.
  Definition Pos_eqb_equation_4_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma Pos_eqb_equation_4)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate Pos_eqb_equation_4_P : eqns_implicit.
  Definition Pos_eqb_equation_5_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma Pos_eqb_equation_5)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate Pos_eqb_equation_5_P : eqns_implicit.
  Definition Pos_eqb_equation_6_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma Pos_eqb_equation_6)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate Pos_eqb_equation_6_P : eqns_implicit.
  Definition Pos_eqb_equation_7_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma Pos_eqb_equation_7)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate Pos_eqb_equation_7_P : eqns_implicit.
  Definition Pos_eqb_equation_8_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma Pos_eqb_equation_8)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate Pos_eqb_equation_8_P : eqns_implicit.
  Definition Pos_eqb_equation_9_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma Pos_eqb_equation_9)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate Pos_eqb_equation_9_P : eqns_implicit.

  Hint Resolve Pos_eqb_equation_1.
  Hint Resolve Pos_eqb_equation_2.
  Hint Resolve Pos_eqb_equation_3.
  Hint Resolve Pos_eqb_equation_4.
  Hint Resolve Pos_eqb_equation_5.
  Hint Resolve Pos_eqb_equation_6.
  Hint Resolve Pos_eqb_equation_7.
  Hint Resolve Pos_eqb_equation_8.
  Hint Resolve Pos_eqb_equation_9.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":9, "ms":9, "hammer":9, "crush":7} *)
  Lemma Pos_eqb_spec : 
    forall l r,
      Pos_eqb l r = true <-> l = r.
  Proof.
    induction l;
    induction r;
    hammer'.
    Restart.

    induction l;
    induction r;
    crush'.
    Restart.

    induction l;
    induction r;
    mirrorsolve.

  Qed.

  Hint Immediate Pos_eqb_spec : eqns_explicit.
  Definition Pos_eqb_spec_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma Pos_eqb_spec)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate Pos_eqb_spec_P : eqns_implicit.

  (* Hint Immediate Pos_eqb_spec : eqns_small. *)
  Hint Resolve Pos_eqb_spec.

  (* Hint Immediate not_trivially_empty_equation_1 : eqns_small.
  Hint Immediate not_trivially_empty_equation_2 : eqns_small.
  Hint Immediate not_trivially_empty_equation_3 : eqns_small.
  Hint Immediate not_trivially_empty_equation_4 : eqns_small. *)

  Definition not_trivially_empty_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma not_trivially_empty_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate not_trivially_empty_equation_1_P : eqns_implicit.
  Definition not_trivially_empty_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma not_trivially_empty_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate not_trivially_empty_equation_2_P : eqns_implicit.
  Definition not_trivially_empty_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma not_trivially_empty_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate not_trivially_empty_equation_3_P : eqns_implicit.
  Definition not_trivially_empty_equation_4_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma not_trivially_empty_equation_4)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate not_trivially_empty_equation_4_P : eqns_implicit.

  (* Hint Immediate gso' : eqns_small. *)

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":2, "hammer":0, "crush":0} *)
  Theorem gso:
    forall (i j: positive) (x: A) (m: tree A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    induction m;
    hammer'.
    Restart.
    induction m;
    crush'.
    Restart.
    induction m;
    mirrorsolve.
  Time Qed.

  Hint Resolve gso : eqns_explicit.
  Definition gso_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma gso)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate gso_P : eqns_implicit.
  
  (* Hint Resolve gso : eqns_small. *)
  Hint Immediate gso.

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":1, "ms":1, "hammer":0, "crush":0} *)
  Theorem gsspec:
    forall (i j: positive) (x: A) (m: tree A),
    get i (set j x m) = ite (Pos_eqb i j) (Some x) (get i m).
  Proof.
    hammer'.
    Restart.
    crush'.
    Restart.
    mirrorsolve.
  Qed.

  Hint Immediate gsspec : eqns_explicit.
  Definition gsspec_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma gsspec)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate gsspec_P : eqns_implicit.
  Hint Resolve gsspec.

  (* 3 equations *)
  MetaCoq Run (infer_equations get_pos_default).

  Hint Immediate get_pos_default_equation_1 : eqns_explicit.
  Hint Immediate get_pos_default_equation_2 : eqns_explicit.
  Hint Immediate get_pos_default_equation_3 : eqns_explicit.

  Hint Resolve get_pos_default_equation_1.
  Hint Resolve get_pos_default_equation_2.
  Hint Resolve get_pos_default_equation_3.

  Hint Immediate not_trivially_empty_equation_1 : eqns_explicit.
  Hint Immediate not_trivially_empty_equation_2 : eqns_explicit.
  Hint Immediate not_trivially_empty_equation_3 : eqns_explicit.
  Hint Immediate not_trivially_empty_equation_4 : eqns_explicit.

  Hint Immediate Node_equation_1 : eqns_explicit.
  Hint Immediate Node_equation_2 : eqns_explicit.
  Hint Immediate Node_equation_3 : eqns_explicit.
  Hint Immediate Node_equation_4 : eqns_explicit.
  Hint Immediate Node_equation_5 : eqns_explicit.
  Hint Immediate Node_equation_6 : eqns_explicit.
  Hint Immediate Node_equation_7 : eqns_explicit.
  Hint Immediate Node_equation_8 : eqns_explicit.

  Hint Resolve not_trivially_empty_equation_1.
  Hint Resolve not_trivially_empty_equation_2.
  Hint Resolve not_trivially_empty_equation_3.
  Hint Resolve not_trivially_empty_equation_4.

  Hint Resolve Node_equation_1.
  Hint Resolve Node_equation_2.
  Hint Resolve Node_equation_3.
  Hint Resolve Node_equation_4.
  Hint Resolve Node_equation_5.
  Hint Resolve Node_equation_6.
  Hint Resolve Node_equation_7.
  Hint Resolve Node_equation_8.

  Definition Node_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma Node_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate Node_equation_1_P : eqns_implicit.
  Definition Node_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma Node_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate Node_equation_2_P : eqns_implicit.
  Definition Node_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma Node_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate Node_equation_3_P : eqns_implicit.
  Definition Node_equation_4_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma Node_equation_4)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate Node_equation_4_P : eqns_implicit.
  Definition Node_equation_5_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma Node_equation_5)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate Node_equation_5_P : eqns_implicit.
  Definition Node_equation_6_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma Node_equation_6)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate Node_equation_6_P : eqns_implicit.
  Definition Node_equation_7_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma Node_equation_7)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate Node_equation_7_P : eqns_implicit.
  Definition Node_equation_8_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma Node_equation_8)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate Node_equation_8_P : eqns_implicit.
  Definition get_pos_default_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get_pos_default_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get_pos_default_equation_1_P : eqns_implicit.
  Definition get_pos_default_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get_pos_default_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get_pos_default_equation_2_P : eqns_implicit.
  Definition get_pos_default_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get_pos_default_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get_pos_default_equation_3_P : eqns_implicit.

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":3, "ms":3, "hammer":0, "crush":0} *)
  Lemma gNode:
    forall (i: positive) (l: tree A) (x: option A) (r: tree A),
    get i (Node l x r) = get_pos_default i x l r.
  Proof.
    induction i;
    hammer'.
    Restart.
    induction i;
    crush'.
    Restart.
    induction i;
    mirrorsolve.
  Qed.

  Hint Immediate gNode : eqns_explicit.
  Hint Resolve gNode.

  Hint Immediate rem'_equation_1 : eqns_explicit.
  Hint Immediate rem'_equation_2 : eqns_explicit.
  Hint Immediate rem'_equation_3 : eqns_explicit.
  Hint Immediate rem'_equation_4 : eqns_explicit.
  Hint Immediate rem'_equation_5 : eqns_explicit.
  Hint Immediate rem'_equation_6 : eqns_explicit.
  Hint Immediate rem'_equation_7 : eqns_explicit.
  Hint Immediate rem'_equation_8 : eqns_explicit.
  Hint Immediate rem'_equation_9 : eqns_explicit.
  Hint Immediate rem'_equation_10 : eqns_explicit.
  Hint Immediate rem'_equation_11 : eqns_explicit.
  Hint Immediate rem'_equation_12 : eqns_explicit.
  Hint Immediate rem'_equation_13 : eqns_explicit.
  Hint Immediate rem'_equation_14 : eqns_explicit.
  Hint Immediate rem'_equation_15 : eqns_explicit.
  Hint Immediate rem'_equation_16 : eqns_explicit.
  Hint Immediate rem'_equation_17 : eqns_explicit.
  Hint Immediate rem'_equation_18 : eqns_explicit.
  Hint Immediate rem'_equation_19 : eqns_explicit.
  Hint Immediate rem'_equation_20 : eqns_explicit.
  Hint Immediate rem'_equation_21 : eqns_explicit.

  Definition gNode_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma gNode)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate gNode_P : eqns_implicit.
  Definition rem'_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_1_P : eqns_implicit.
  Definition rem'_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_2_P : eqns_implicit.
  Definition rem'_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_3_P : eqns_implicit.
  Definition rem'_equation_4_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_4)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_4_P : eqns_implicit.
  Definition rem'_equation_5_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_5)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_5_P : eqns_implicit.
  Definition rem'_equation_6_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_6)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_6_P : eqns_implicit.
  Definition rem'_equation_7_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_7)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_7_P : eqns_implicit.
  Definition rem'_equation_8_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_8)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_8_P : eqns_implicit.
  Definition rem'_equation_9_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_9)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_9_P : eqns_implicit.
  Definition rem'_equation_10_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_10)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_10_P : eqns_implicit.
  Definition rem'_equation_11_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_11)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_11_P : eqns_implicit.
  Definition rem'_equation_12_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_12)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_12_P : eqns_implicit.
  Definition rem'_equation_13_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_13)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_13_P : eqns_implicit.
  Definition rem'_equation_14_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_14)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_14_P : eqns_implicit.
  Definition rem'_equation_15_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_15)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_15_P : eqns_implicit.
  Definition rem'_equation_16_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_16)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_16_P : eqns_implicit.
  Definition rem'_equation_17_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_17)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_17_P : eqns_implicit.
  Definition rem'_equation_18_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_18)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_18_P : eqns_implicit.
  Definition rem'_equation_19_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_19)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_19_P : eqns_implicit.
  Definition rem'_equation_20_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_20)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_20_P : eqns_implicit.
  Definition rem'_equation_21_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma rem'_equation_21)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate rem'_equation_21_P : eqns_implicit.


  (* MS TODO tactics *)
  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":1, "ms":1, "hammer":0, "crush":0} *)
  Lemma get_Node_1 : 
    forall l x r, get xH (Node l x r) = x.
  Proof.
    hammer'.
    Restart.
    crush'.
    Restart.
    mirrorsolve.
  Qed.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":8, "ms":8, "hammer":0, "crush":0} *)
  
  Lemma get_Node_l : 
    forall l x r i, get i~0 (Node l x r) = get i l.
  Proof.
    hammer'.
    Restart.
    crush'.
    Restart.
    mirrorsolve.
  Qed.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":8, "ms":8, "hammer":0, "crush":0} *)
  
  Lemma get_Node_r : 
    forall l x r i, get i~1 (Node l x r) = get i r.
  Proof.
    hammer'.
    Restart.
    crush'.
    Restart.
    mirrorsolve.
  Qed.

  Hint Immediate get_Node_1 : eqns_explicit.
  Hint Immediate get_Node_l : eqns_explicit.
  Hint Immediate get_Node_r : eqns_explicit.

  Definition get_Node_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get_Node_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get_Node_1_P : eqns_implicit.
  Definition get_Node_l_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get_Node_l)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get_Node_l_P : eqns_implicit.
  Definition get_Node_r_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get_Node_r)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get_Node_r_P : eqns_implicit.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":21, "ms":21, "hammer":0, "crush":0} *)
  Lemma get_rem' : 
    forall i t, 
      get i (rem' i t) = None.
  Proof.
    induction i;
    induction t;
    hammer'.
    Restart.
    induction i;
    induction t;
    crush'.
    Restart.
    induction i;
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate get_rem' : eqns_explicit.
  Hint Resolve get_rem'.

  Definition get_rem'_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get_rem')); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get_rem'_P : eqns_implicit.
  (* Hint Immediate remove'_equation_1: eqns_explicit. *)

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma remove'_equation_ext: 
    forall p t, remove' p t = rem' p t.
  Proof.
    intros;
    eapply eq_refl.
  Qed.

  Hint Immediate remove'_equation_ext : eqns_explicit.

  Hint Immediate remove_equation_1: eqns_explicit.
  Hint Immediate remove_equation_2: eqns_explicit.

  Definition remove'_equation_ext_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma remove'_equation_ext)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate remove'_equation_ext_P : eqns_implicit.
  Definition remove_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma remove_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate remove_equation_1_P : eqns_implicit.
  Definition remove_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma remove_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate remove_equation_2_P : eqns_implicit.

  (*** MS EFFORT {"type": "edit"} *)
  (* MS TODO tactics *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":2, "hammer":0, "crush":0} *)
  Theorem grs:
    forall (m: tree A) (i: positive), get i (remove i m) = None.
  Proof.
    induction m;
    hammer'.
    Restart.
    induction m;
    crush'.
    Restart.
    induction m;
    mirrorsolve.
  Qed.

  Hint Immediate grs : eqns_explicit.
  Definition grs_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma grs)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate grs_P : eqns_implicit.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":21, "ms":21, "hammer":0, "crush":0} *)
  (* Lemma get_rem'_o : 
    forall i j t, 
      i <> j ->
      get i (rem' j t) = get i t.
  Proof.
    induction i;
    induction t;
    mirrorsolve.
  Qed. *)

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":8, "ms":8, "hammer":0, "crush":0} *)
  Lemma remove_Node_1 : 
    forall l x r, remove xH (Node l x r) = Node l None r.
  Proof.
    induction l;
    induction x;
    induction r;
    hammer'.
    Restart.
    induction l;
    induction x;
    induction r;
    crush'.
    Restart.
    induction l;
    induction x;
    induction r;
    mirrorsolve.
  Qed.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":8, "ms":8, "hammer":0, "crush":0} *)
  Lemma remove_Node_l : 
    forall l x r i, remove i~0 (Node l x r) = Node (remove i l) x r.
  Proof.
    induction l;
    induction x;
    induction r;
    hammer'.
    Restart.
    induction l;
    induction x;
    induction r;
    crush'.
    Restart.
    induction l;
    induction x;
    induction r;
    mirrorsolve.
  Qed.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":8, "ms":8, "hammer":0, "crush":0} *)
  Lemma remove_Node_r : 
    forall l x r i, remove i~1 (Node l x r) = Node l x (remove i r).
  Proof.
    induction l;
    induction x;
    induction r;
    hammer'.
    Restart.
    induction l;
    induction x;
    induction r;
    crush'.
    Restart.
    induction l;
    induction x;
    induction r;
    mirrorsolve.
  Qed.

  Hint Immediate remove_Node_1 : eqns_explicit.
  Hint Immediate remove_Node_l : eqns_explicit.
  Hint Immediate remove_Node_r : eqns_explicit.

  Definition remove_Node_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma remove_Node_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate remove_Node_1_P : eqns_implicit.
  Definition remove_Node_l_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma remove_Node_l)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate remove_Node_l_P : eqns_implicit.
  Definition remove_Node_r_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma remove_Node_r)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate remove_Node_r_P : eqns_implicit.

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":63, "ms":63, "hammer":0, "crush":0} *)
  Lemma gro': 
    forall i j t,
      i <> j -> get i (remove' j t) = get' i t.
  Proof.
    induction i;
    induction j;
    induction t;
    hammer'.
    Restart.
    induction i;
    induction j;
    induction t;
    crush'.
    Restart.
    induction i;
    induction j;
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate gro' : eqns_explicit.
  (* Hint Immediate gro' : eqns_small. *)
  Hint Resolve gro'.

  Definition gro'_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma gro')); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate gro'_P : eqns_implicit.

  (*** MS EFFORT {"type": "edit"} *)
  (* MS TODO tactics *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":2, "hammer":0, "crush":0} *)
  
  Theorem gro:
    forall (i j: positive) (m: tree A),
    i <> j -> get i (remove j m) = get i m.
  Proof.
    induction m;
    hammer'.
    Restart.
    induction m;
    crush'.
    Restart.
    induction m;
    mirrorsolve.
  Qed.

  Hint Immediate grs : eqns_explicit.
  Hint Immediate gro : eqns_explicit.

  Hint Immediate grs_P : eqns_implicit.
  Definition gro_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma gro)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate gro_P : eqns_implicit.

  (*** MS EFFORT {"type": "edit"} *)
  (* MS TODO tactics *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":1, "ms":1, "hammer":0, "crush":0} *)
  Theorem grspec:
    forall i j (m: tree A),
    get i (remove j m) = ite (Pos_eqb i j) None (get i m).
  Proof.
    hammer'.
    Restart.
    crush'.
    Restart.
    mirrorsolve.
  Qed.

  Hint Immediate grspec : eqns_explicit.
  Definition grspec_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma grspec)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate grspec_P : eqns_implicit.

(** ** Custom case analysis principles and induction principles *)

(** We can view trees as being of one of two (non-exclusive)
    cases: either [Empty] for an empty tree, or [Node l o r] for a
    nonempty tree, with [l] and [r] the left and right subtrees
    and [o] an optional value.  The [Empty] constructor and the [Node]
    smart function defined above provide one half of the view: the one
    that lets us construct values of type [tree A].

    We now define the other half of the view: the one that lets us
    inspect and recurse over values of type [tree A].  This is achieved
    by defining appropriate principles for case analysis and induction. *)

  (** A case analysis principle *)


  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":8, "ms":8, "hammer":8, "crush":8} *)
  Lemma unroll_tree_case: forall l o r,
    not_trivially_empty l o r ->
    tree_case (Node l o r) = node' l o r.
  Proof.
    induction l;
    induction o;
    induction r;
    hammer'.
    Restart.
    induction l;
    induction o;
    induction r;
    crush'.
    Restart.
    induction l;
    induction o;
    induction r;
    mirrorsolve.
  Qed.

  Hint Immediate unroll_tree_case : eqns_explicit.
  (* Hint Immediate unroll_tree_case : eqns_small. *)
  Definition unroll_tree_case_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma unroll_tree_case)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate unroll_tree_case_P : eqns_implicit.

  (** A recursion principle *)

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":8, "ms":8, "hammer":8, "crush":8} *)
  
  Hint Immediate tree_rec'_equation_1 : eqns_explicit.
  Hint Immediate tree_rec'_equation_2 : eqns_explicit.

  Definition tree_rec'_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma tree_rec'_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate tree_rec'_equation_1_P : eqns_implicit.
  Definition tree_rec'_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma tree_rec'_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate tree_rec'_equation_2_P : eqns_implicit.

  Lemma unroll_tree_rec: forall l o r,
    not_trivially_empty l o r ->
    tree_rec' (Node l o r) = node_rec' l (tree_rec' l) o r (tree_rec' r).
  Proof.
    induction l;
    induction o;
    induction r;
    hammer'.
    Restart.
    induction l;
    induction o;
    induction r;
    crush'.
    Restart.
    induction l;
    induction o;
    induction r;
    mirrorsolve.
  Qed.

  (* Hint Immediate unroll_tree_rec : eqns_implicit.
  Definition unroll_tree_rec_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma unroll_tree_rec)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate unroll_tree_rec_P : eqns_implicit. *)

  (** A double recursion principle *)

  (* 
      MIRRORSOLVE @TODO: adapt these
  *)
(* 
  Context {A B C: Type}
          (base: C)
          (base1: tree B -> C) 
          (base2: tree A -> C)
          (nodes: forall (l1: tree A) (o1: option A) (r1: tree A)
                         (l2: tree B) (o2: option B) (r2: tree B)
                         (lrec: C) (rrec: C), C).

  Fixpoint tree_rec2' (m1: tree' A) (m2: tree' B) : C.
  Proof.
    destruct m1 as [ r1 | x1 | x1 r1 | l1 | l1 r1 | l1 x1 | l1 x1 r1 ];
    destruct m2 as [ r2 | x2 | x2 r2 | l2 | l2 r2 | l2 x2 | l2 x2 r2 ];
    (apply nodes;
    [ solve [ exact (Nodes l1) | exact Empty ]
    | solve [ exact (Some x1)  | exact None ]
    | solve [ exact (Nodes r1) | exact Empty ]
    | solve [ exact (Nodes l2) | exact Empty ]
    | solve [ exact (Some x2)  | exact None ]
    | solve [ exact (Nodes r2) | exact Empty ]
    | solve [ exact (tree_rec2' l1 l2) | exact (base2 (Nodes l1)) | exact (base1 (Nodes l2)) | exact base ]
    | solve [ exact (tree_rec2' r1 r2) | exact (base2 (Nodes r1)) | exact (base1 (Nodes r2)) | exact base ]
    ]).
  Defined. *)

  (* Definition tree_rec2 (a: tree A) (b: tree B) : C :=
    match a, b with
    | Empty, Empty => base
    | Empty, _ => base1 b
    | _, Empty => base2 a
    | Nodes a', Nodes b' => tree_rec2' a' b'
    end. *)

    (*** MS LEMMA {"original": True, "sfo": True, "tsfo": False, "ho": False, "goals":1, "ms":0, "hammer":0, "crush":0} *)
(* 
  Lemma unroll_tree_rec2_NE:
    forall l1 o1 r1,
    not_trivially_empty l1 o1 r1 ->
    tree_rec2 (Node l1 o1 r1) Empty = base2 (Node l1 o1 r1).
  Proof.
    intros. destruct l1, o1, r1; try contradiction; reflexivity.
  Qed. *)

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": False, "ho": False, "goals":1, "ms":0, "hammer":0, "crush":0} *)

  (* Lemma unroll_tree_rec2_EN:
    forall l2 o2 r2,
    not_trivially_empty l2 o2 r2 ->
    tree_rec2 Empty (Node l2 o2 r2) = base1 (Node l2 o2 r2).
  Proof.
    intros. destruct l2, o2, r2; try contradiction; reflexivity.
  Qed. *)

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": False, "ho": False, "goals":1, "ms":0, "hammer":0, "crush":0} *)
  (* Lemma unroll_tree_rec2_NN:
    forall l1 o1 r1 l2 o2 r2,
    not_trivially_empty l1 o1 r1 -> not_trivially_empty l2 o2 r2 ->
    tree_rec2 (Node l1 o1 r1) (Node l2 o2 r2) =
    nodes l1 o1 r1 l2 o2 r2 (tree_rec2 l1 l2) (tree_rec2 r1 r2).
  Proof.
    intros.
    destruct l1, o1, r1; try contradiction; destruct l2, o2, r2; try contradiction; reflexivity.
  Qed. *)

  (* End TREE_REC2.  *)

(** An induction principle *)

  (* Section TREE_IND.

  Context {A: Type} (P: tree A -> Type)
          (empty: P Empty)
          (node: forall l, P l -> forall o r, P r -> not_trivially_empty l o r ->
                 P (Node l o r)).

  Program Fixpoint tree_ind' (m: tree' A) : P (Nodes m) :=
    match m with
    | Node001 r => @node Empty empty None (Nodes r) (tree_ind' r) _
    | Node010 x => @node Empty empty (Some x) Empty empty _
    | Node011 x r => @node Empty empty (Some x) (Nodes r) (tree_ind' r) _
    | Node100 l => @node (Nodes l) (tree_ind' l) None Empty empty _
    | Node101 l r => @node (Nodes l) (tree_ind' l) None (Nodes r) (tree_ind' r) _
    | Node110 l x => @node (Nodes l) (tree_ind' l) (Some x) Empty empty _
    | Node111 l x r => @node (Nodes l) (tree_ind' l) (Some x) (Nodes r) (tree_ind' r) _
    end.

  Definition tree_ind (m: tree A) : P m :=
    match m with
    | Empty => empty
    | Nodes m' => tree_ind' m'
    end.

  End TREE_IND. *)

(** ** Extensionality property *)

  Set MirrorSolve Solver "cvc5".
  Set MirrorSolve Solver Flags "--tlimit=5000".

  (*** MS EFFORT {"type": "edit"} *)
 (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":6, "ms":5, "hammer":0, "crush":0} *)
  Lemma tree'_not_empty:
    forall (m: tree' A), 
      ~ (forall i, get' i m = None).
  Proof.
    induction m;
    hammer'.
    Restart.
    induction m;
    crush'.
    Restart.
    induction m;
    mirrorsolve.
  Admitted.

  Hint Immediate tree'_not_empty : eqns_explicit.
  Definition tree'_not_empty_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma tree'_not_empty)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate tree'_not_empty_P : eqns_implicit.


  (*** MS EFFORT {"type": "edit"} *)
 (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":1, "hammer":0, "crush":0} *)
  Corollary extensionality_empty:
    forall (m: tree A),
    (forall i, get i m = None) -> m = Empty.
  Proof.
    induction m;
    hammer'.
    Restart.
    induction m;
    crush'.
    Restart.
    induction m;
    mirrorsolve.
  Admitted.

  (* Hint Immediate extensionality_empty : eqns_small.
  Hint Immediate extensionality_empty : eqns_explicit. *)

  (*** MS EFFORT {"type": "edit"} *)
 (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":4, "ms":1, "hammer":0, "crush":0} *)
  Theorem extensionality:
    forall (m1 m2: tree A),
    (forall i, get i m1 = get i m2) -> m1 = m2.
  Proof.
    induction m1; 
    induction m2;
    hammer'.
    Restart.
    induction m1; 
    induction m2;
    crush'.
    Restart.
    induction m1; 
    induction m2;
    mirrorsolve.
  Admitted.

  (* Hint Immediate extensionality : eqns_explicit.
  Hint Immediate extensionality : eqns_small. *)
  (** Some consequences of extensionality *)

  (*** MS EFFORT {"type": "edit"} *)
 (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":1, "ms":0, "hammer":0, "crush":0} *)
  Theorem gsident:
    forall (i: positive) (m: tree A) (v: A),
    get i m = Some v -> set i v m = m.
  Proof.
    intros.
    eapply extensionality.
    mirrorsolve.
  Qed.

  Hint Immediate gsident : eqns_explicit.
  Definition gsident_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma gsident)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate gsident_P : eqns_implicit.

  (*** MS EFFORT {"type": "edit"} *)
 (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":1, "ms":0, "hammer":0, "crush":0} *)
  Theorem set2:
    forall i (m: tree A) (v1 v2: A),
      set i v2 (set i v1 m) = set i v2 m.
  Proof.
    intros; 
    eapply extensionality.
    mirrorsolve.
  Qed.

  Hint Immediate set2 : eqns_explicit.
  Hint Resolve set2.

  Definition set2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma set2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate set2_P : eqns_implicit.


(** ** Boolean equality *)

  (* Hypothesis (beqA_spec: (forall x y, beqA x y = true <-> x = y)). *)

  Axiom beqA'_spec : (forall x y, beqA' x y = true <-> x = y).
  (* Admitted. *)
  (* Proof.
    intros.
    eapply beqA_spec.
  Qed. *)
  Hint Immediate beqA'_spec : eqns_explicit.
  (* Hint Immediate beqA'_spec : eqns_small. *)
  Definition beqA'_spec_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beqA'_spec)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beqA'_spec_P : eqns_implicit.


    (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":49, "ms":49, "hammer":0, "crush":0} *)
  Lemma beq'_eq_spec : 
    forall l r,
      beq' l r = true <-> l = r.
  Proof.
    induction l;
    induction r;
    hammer'.
    Restart.
    induction l;
    induction r;
    crush'.
    Restart.
    induction l;
    induction r;
    mirrorsolve.
  Qed.

  Hint Immediate beq'_eq_spec : eqns_explicit.
  (* Hint Immediate beq'_eq_spec : eqns_small. *)
  Hint Resolve beq'_eq_spec.
  Definition beq'_eq_spec_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq'_eq_spec)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq'_eq_spec_P : eqns_implicit.


  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":4, "ms":4, "hammer":0, "crush":0} *)
  Lemma beq_eq_spec : 
    forall m1 m2,
      beq m1 m2 = true <-> m1 = m2.
  Proof.
    induction m1;
    induction m2;
    hammer'.
    Restart.
    induction m1;
    induction m2;
    crush'.
    Restart.
    induction m1;
    induction m2;
    mirrorsolve.
  Qed.

  Hint Immediate beq_eq_spec : eqns_explicit.
  Hint Resolve beq_eq_spec.

  Definition beq_eq_spec_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq_eq_spec)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq_eq_spec_P : eqns_implicit.

  (* Lemma beq_optA_spec:
    forall l r,
      beq_optA l r = true <-> l = r *)

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":64, "ms":64, "hammer":0, "crush":0} *)
  Lemma beq_NN: 
    forall l1 o1 r1 l2 o2 r2,
      not_trivially_empty l1 o1 r1 ->
      not_trivially_empty l2 o2 r2 ->
      beq (Node l1 o1 r1) (Node l2 o2 r2) =
      (beq l1 l2 && beq_optA o1 o2 && beq r1 r2)%bool.
  Proof.

    induction l1; 
    induction o1;
    induction r1;
    induction l2;
    induction o2;
    induction r2;
    hammer'.
    Restart.
    induction l1; 
    induction o1;
    induction r1;
    induction l2;
    induction o2;
    induction r2;
    crush'.
    Restart.
    time "boolean queries" (
    induction l1; 
    induction o1;
    induction r1;
    induction l2;
    induction o2;
    induction r2;
    mirrorsolve).

  Time Qed.

  Hint Immediate beq_NN : eqns_explicit.
  Definition beq_NN_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq_NN)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq_NN_P : eqns_implicit.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":2, "hammer":0, "crush":0} *)
  Lemma beq_optA_resp:
    forall m x, 
      beq_optA (get x m) (get x m) = true.
  Proof.
    induction m;
    hammer'.
    Restart.
    induction m;
    crush'.
    Restart.
    induction m; 
    mirrorsolve.
  Qed.

  Hint Immediate beq_optA_resp : eqns_explicit.
  Definition beq_optA_resp_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma beq_optA_resp)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate beq_optA_resp_P : eqns_implicit.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":1, "ms":0, "hammer":0, "crush":0} *)
  Lemma beq_optA_spec:
    forall l r, 
      (forall x, beq_optA (get x l) (get x r) = true) -> 
      l = r.
  Proof.
    intros.
    eapply extensionality.
    mirrorsolve.
  Qed.

  (* Hint Immediate beq_optA_spec : eqns_explicit.
  Hint Immediate beq_optA_spec : eqns_small. *)

(*** MS EFFORT {"type": "edit"} *)
 (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":1, "ms":0, "hammer":0, "crush":0} *)
  
  Lemma beq_correct_bool:
    forall m1 m2,
    beq m1 m2 = true <-> (forall x, beq_optA (get x m1) (get x m2) = true).
  Proof.
    mirrorsolve.
  Admitted.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma get_eq_booL_eqn_1 : 
    forall x m1 m2 y1 y2, 
      get x m1 = Some y1 -> 
      get x m2 = Some y2 -> 
      get_eq_bool x m1 m2 <-> beqA' y1 y2 = true.
  Proof.
    intros.
    unfold get_eq_bool.
    erewrite H.
    erewrite H0.
    eapply iff_refl.
  Qed.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma get_eq_booL_eqn_2 : 
    forall x m1 m2 y, 
      get x m1 = Some y -> 
      get x m2 = None -> 
      get_eq_bool x m1 m2 <-> False.
  Proof.
    intros.
    unfold get_eq_bool.
    erewrite H.
    erewrite H0.
    eapply iff_refl.
  Qed.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma get_eq_booL_eqn_3 : 
    forall x m1 m2 y, 
      get x m1 = None -> 
      get x m2 = Some y -> 
      get_eq_bool x m1 m2 <-> False.
  Proof.
    intros.
    unfold get_eq_bool.
    erewrite H.
    erewrite H0.
    eapply iff_refl.
  Qed.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma get_eq_booL_eqn_4 : 
    forall x m1 m2, 
      get x m1 = None -> 
      get x m2 = None -> 
      get_eq_bool x m1 m2 <-> True.
  Proof.
    intros.
    unfold get_eq_bool.
    erewrite H.
    erewrite H0.
    eapply iff_refl.
  Qed.

  Hint Immediate get_eq_booL_eqn_1 : eqns_explicit.
  Hint Immediate get_eq_booL_eqn_2 : eqns_explicit.
  Hint Immediate get_eq_booL_eqn_3 : eqns_explicit.
  Hint Immediate get_eq_booL_eqn_4 : eqns_explicit.

  Definition get_eq_booL_eqn_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get_eq_booL_eqn_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get_eq_booL_eqn_1_P : eqns_implicit.
  Definition get_eq_booL_eqn_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get_eq_booL_eqn_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get_eq_booL_eqn_2_P : eqns_implicit.
  Definition get_eq_booL_eqn_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get_eq_booL_eqn_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get_eq_booL_eqn_3_P : eqns_implicit.
  Definition get_eq_booL_eqn_4_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma get_eq_booL_eqn_4)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate get_eq_booL_eqn_4_P : eqns_implicit.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":16, "ms":13, "hammer":0, "crush":0} *)
  Lemma get_eq_bool_spec: 
    forall l r,
      l = r <-> (forall x, get_eq_bool x l r).
  Proof.
    induction l;
    induction r;
    split;
    try (induction x);
    mirrorsolve.
  Admitted.

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":1, "ms":0, "hammer":0, "crush":0} *)
    Theorem beq_correct:
      forall m1 m2,
      beq m1 m2 = true <->
      (forall x, get_eq_bool x m1 m2).
    Proof.
      intros.
      erewrite <- get_eq_bool_spec.
      mirrorsolve.
    Qed.

(** ** Collective operations *)

  (* MetaCoq Run (infer_equations prev). *)

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma prev_eqn: 
    forall i, 
      prev i = prev_append i xH.
  Proof.
    intros;
    eapply eq_refl.
  Qed.

  Hint Immediate prev_eqn : eqns_explicit.
  Hint Resolve prev_eqn.
  Definition prev_eqn_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma prev_eqn)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate prev_eqn_P : eqns_implicit.

  (* Set MirrorSolve Query Debug. *)

  MetaCoq Run (infer_equations prev_append).

  Hint Immediate prev_append_equation_1 : eqns_explicit.
  Hint Resolve prev_append_equation_1.
  Hint Immediate prev_append_equation_2 : eqns_explicit.
  Hint Resolve prev_append_equation_2.
  Hint Immediate prev_append_equation_3 : eqns_explicit.
  Hint Resolve prev_append_equation_3.

  Definition prev_append_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma prev_append_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate prev_append_equation_1_P : eqns_implicit.
  Definition prev_append_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma prev_append_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate prev_append_equation_2_P : eqns_implicit.
  Definition prev_append_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma prev_append_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate prev_append_equation_3_P : eqns_implicit.
    
  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":3, "ms":3, "hammer":0, "crush":0} *)
  Lemma prev_append_prev:
    forall i j,
      prev (prev_append i j) = prev_append j i.
  Proof.
    induction i; mirrorsolve.
  Qed.

  Hint Immediate prev_append_prev : eqns_explicit.
  Hint Resolve prev_append_prev.
  Definition prev_append_prev_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma prev_append_prev)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate prev_append_prev_P : eqns_implicit.

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":1, "ms":1, "hammer":0, "crush":0} *)
  Lemma prev_involutive :
    forall i, 
      prev (prev i) = i.
  Proof.
    mirrorsolve.
  Qed.

  Hint Immediate prev_involutive : eqns_explicit.
  Hint Resolve prev_involutive.

  Definition prev_involutive_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma prev_involutive)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate prev_involutive_P : eqns_implicit.

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  Lemma prev_append_inj :
    forall i j j', 
      prev_append i j = prev_append i j' -> 
      j = j'.
  Proof.
    induction i; 
    mirrorsolve.
  Qed.



  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  (* Lemma gmap':
    forall (i j : positive) (m: tree' A),
    get' i (map' m j) = option_map (prev (prev_append i j)) (get' i m).
  Proof.
  Admitted. *)

  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  (* Theorem gmap:
    forall {A B} (f: positive -> A -> B) (i: positive) (m: t A),
    get i (map f m) = option_map (f i) (get i m).
  Proof.
    intros; destruct m as [|m]; simpl. auto. rewrite gmap'. repeat f_equal. exact (prev_involutive i).
  Qed. *)

  

  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  (* Theorem gmap1:
    forall {A B} (f: A -> B) (i: elt) (m: t A),
    get i (map1 f m) = option_map f (get i m).
  Proof.
    intros. destruct m as [|m]; simpl. auto.
    revert i; induction m; destruct i; simpl; auto.
  Qed. *)

  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  (* Lemma gmap_filter1:
    forall {A B} (f: A -> option B) (m: tree A) (i: positive),
    get i (map_filter1 f m) = match get i m with None => None | Some a => f a end.
  Proof.
    change @map_filter1 with @map_filter1_nonopt. unfold map_filter1_nonopt.
    intros until f. induction m using tree_ind; intros.
  - auto.
  - rewrite unroll_tree_rec by auto. rewrite ! gNode; destruct i; auto.
  Qed. *)

  (* Definition filter1 {A} (pred: A -> bool) (m: t A) : t A :=
    map_filter1 (fun a => if pred a then Some a else None) m. *)

  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  (* Theorem gfilter1:
    forall {A} (pred: A -> bool) (i: elt) (m: t A),
    get i (filter1 pred m) =
    match get i m with None => None | Some x => if pred x then Some x else None end.
  Proof.
    intros. apply gmap_filter1.
  Qed.  *)

  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  (* Lemma gcombine_l: forall m i, get i (combine_l m) = f (get i m) None.
  Proof.
    intros; unfold combine_l; rewrite gmap_filter1. destruct (get i m); auto.
  Qed. *)

  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  (* Lemma gcombine_r: forall m i, get i (combine_r m) = f None (get i m).
  Proof.
    intros; unfold combine_r; rewrite gmap_filter1. destruct (get i m); auto.
  Qed. *)

  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  (* Theorem gcombine:
      forall (m1: t A) (m2: t B) (i: positive),
      get i (combine m1 m2) = f (get i m1) (get i m2).
  Proof.
    change combine with combine_nonopt.
    induction m1 using tree_ind; induction m2 using tree_ind; intros.
  - auto.
  - unfold combine_nonopt; rewrite unroll_tree_rec2_EN by auto. apply gcombine_r.
  - unfold combine_nonopt; rewrite unroll_tree_rec2_NE by auto. apply gcombine_l.
  - unfold combine_nonopt; rewrite unroll_tree_rec2_NN by auto.
    rewrite ! gNode; destruct i; auto. destruct o, o0; auto.
  Qed. *)

  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": True, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  (* Theorem combine_commut:
    forall (A B: Type) (f g: option A -> option A -> option B),
    f None None = None -> g None None = None ->
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.
  Proof.
    intros. apply extensionality; intros i. rewrite ! gcombine by auto. auto.
  Qed. *)

(** ** List of all bindings *)

  MetaCoq Run (infer_equations xelements).
  Hint Immediate xelements_equation_1 : eqns_explicit.
  Hint Immediate xelements_equation_2 : eqns_explicit.

  MetaCoq Run (infer_equations xelements').
  Hint Immediate xelements'_equation_1 : eqns_explicit.
  Hint Immediate xelements'_equation_2 : eqns_explicit.
  Hint Immediate xelements'_equation_3 : eqns_explicit.
  Hint Immediate xelements'_equation_4 : eqns_explicit.
  Hint Immediate xelements'_equation_5 : eqns_explicit.
  Hint Immediate xelements'_equation_6 : eqns_explicit.
  Hint Immediate xelements'_equation_7 : eqns_explicit.

  MetaCoq Run (infer_equations app_pos_A).
  Hint Immediate app_pos_A_equation_1 : eqns_explicit.
  Hint Immediate app_pos_A_equation_2 : eqns_explicit.

  Definition app_pos_A_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma app_pos_A_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate app_pos_A_equation_1_P : eqns_implicit.
  Definition app_pos_A_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma app_pos_A_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate app_pos_A_equation_2_P : eqns_implicit.
  Definition xelements'_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma xelements'_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate xelements'_equation_1_P : eqns_implicit.
  Definition xelements'_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma xelements'_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate xelements'_equation_2_P : eqns_implicit.
  Definition xelements'_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma xelements'_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate xelements'_equation_3_P : eqns_implicit.
  Definition xelements'_equation_4_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma xelements'_equation_4)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate xelements'_equation_4_P : eqns_implicit.
  Definition xelements'_equation_5_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma xelements'_equation_5)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate xelements'_equation_5_P : eqns_implicit.
  Definition xelements'_equation_6_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma xelements'_equation_6)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate xelements'_equation_6_P : eqns_implicit.
  Definition xelements'_equation_7_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma xelements'_equation_7)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate xelements'_equation_7_P : eqns_implicit.
  Definition xelements_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma xelements_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate xelements_equation_1_P : eqns_implicit.
  Definition xelements_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma xelements_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate xelements_equation_2_P : eqns_implicit.

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  Lemma xelements'_append:
    forall (m: tree' A) i k1 k2,
      (xelements' m i (app_pos_A k1 k2) = app_pos_A (xelements' m i k1) k2)%list.
  Proof.
    induction m;
    mirrorsolve.
  Qed.

  Hint Immediate xelements'_append : eqns_explicit.
  Definition xelements'_append_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma xelements'_append)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate xelements'_append_P : eqns_implicit.


  MetaCoq Run (infer_equations o2l).
  Hint Immediate o2l_equation_1 : eqns_explicit.
  Hint Immediate o2l_equation_2 : eqns_explicit.

  Definition o2l_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma o2l_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate o2l_equation_1_P : eqns_implicit.
  Definition o2l_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma o2l_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate o2l_equation_2_P : eqns_implicit.


  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":8, "ms":8, "hammer":0, "crush":0} *)
  Lemma xelements_Node:
    forall (l: tree A) (o: option A) (r: tree A) i,
    xelements (Node l o r) i =
      app_pos_A (xelements l (xO i))
      (app_pos_A 
        (o2l i o)
      (xelements r (xI i))).
  Proof.
    induction l;
    induction o;
    induction r;
    mirrorsolve.
  Qed.

  MetaCoq Run (infer_equations In_pos_A).
  Hint Immediate In_pos_A_equation_1 : eqns_small.
  Hint Immediate In_pos_A_equation_2 : eqns_small.

  Definition In_pos_A_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma In_pos_A_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate In_pos_A_equation_1_P : eqns_implicit.
  Definition In_pos_A_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma In_pos_A_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate In_pos_A_equation_2_P : eqns_implicit.


  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":4, "ms":4, "hammer":0, "crush":0} *)
  Lemma in_app_pos_A : 
    forall l r v, 
      In_pos_A v (app_pos_A l r) <-> In_pos_A v l \/ In_pos_A v r.
  Proof.
    induction l;
    induction r;
    mirrorsolve.
  Qed.

  Ltac invert_Node := 
    (erewrite <- Node_equation_1) ||
    (erewrite <- Node_equation_2) ||
    (erewrite <- Node_equation_3) ||
    (erewrite <- Node_equation_4) || 
    (erewrite <- Node_equation_5) ||
    (erewrite <- Node_equation_6) ||
    (erewrite <- Node_equation_7) ||
    (erewrite <- Node_equation_8).

  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": True, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  Lemma nodes_ind:
    forall (P: tree A -> Prop), 
      P Empty -> 
      (forall l o r, not_trivially_empty l o r -> P l -> P r -> P (Node l o r)) -> 
      forall t, P t.
  Proof.
    intros ? ?.
    induction t; trivial.
    induction t; simpl;
    invert_Node; 
    eapply H0;
    simpl;
    intuition eauto.
  Qed.
  
  Hint Immediate in_app_pos_A : eqns_explicit.
  Hint Immediate xelements_Node : eqns_explicit.
  Hint Immediate gNode : eqns_explicit.
  Hint Immediate prev_append_prev : eqns_explicit.

  Definition in_app_pos_A_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma in_app_pos_A)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate in_app_pos_A_P : eqns_implicit.
  Definition xelements_Node_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma xelements_Node)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate xelements_Node_P : eqns_implicit.

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":6, "ms":6, "hammer":0, "crush":0} *)
  Lemma xelements_correct:
    forall (m: tree A) i j v,
      get i m = Some v -> 
      In_pos_A (prev (prev_append i j), v) (xelements m j).
  Proof.
    induction m using nodes_ind;
    try (destruct i);
    mirrorsolve.
  Qed.

  Hint Immediate xelements_correct : eqns_explicit.
  Definition xelements_correct_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma xelements_correct)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate xelements_correct_P : eqns_implicit.


  MetaCoq Run (infer_equations elements).
  Hint Immediate elements_equation_1 : eqns_explicit.
  Hint Immediate elements_equation_2 : eqns_explicit.

  Definition elements_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma elements_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate elements_equation_1_P : eqns_implicit.
  Definition elements_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma elements_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate elements_equation_2_P : eqns_implicit.

  Set MirrorSolve Solver "z3".
  Set MirrorSolve Solver Flags "-T:5".
  
  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":1, "hammer":0, "crush":0} *)
  Theorem elements_correct:
    forall (m: tree A) (i: positive) (v: A),
    get i m = Some v -> In_pos_A (i, v) (elements m).
  Proof.

    destruct m;
    mirrorsolve.
    Restart.

    intros m i v H.
    generalize (xelements_correct m i xH v H). 
    destruct m;
    mirrorsolve.
  Qed.

  Set MirrorSolve Solver "cvc5".
  Set MirrorSolve Solver Flags "--tlimit=5000".

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":1, "hammer":0, "crush":0} *)
  Lemma in_xelements:
    forall (m: tree A) (i k: positive) (v: A),
    In_pos_A (k, v) (xelements m i) ->
    ~ (forall j, ~ (k = prev (prev_append j i) /\ get j m = Some v)).
  Proof.
    induction m using nodes_ind;
    mirrorsolve.
    Restart.
    induction m using nodes_ind.
    - mirrorsolve.
    - intros. 
      rewrite xelements_Node, ! in_app_pos_A in H0.
      destruct H0 as [P | [P | P]];
      mirrorsolve.
  Qed.

  Hint Immediate prev_append_inj : eqns_explicit.
  Definition prev_append_inj_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma prev_append_inj)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate prev_append_inj_P : eqns_implicit.

  Hint Immediate in_xelements : eqns_explicit.
  Definition in_xelements_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma in_xelements)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate in_xelements_P : eqns_implicit.


  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":2, "hammer":0, "crush":0} *)
  Theorem elements_complete:
    forall (m: tree A) (i: positive) (v: A),
    In_pos_A (i, v) (elements m) -> get i m = Some v.
  Proof.
    induction m;
    mirrorsolve.
  Qed.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma xkeys_eqn : 
    forall m i, xkeys m i = map_fst (xelements m i).
  Proof.
    intros.
    exact eq_refl.
  Qed.

  Hint Immediate xkeys_eqn : eqns_explicit.

  MetaCoq Run (infer_equations o2l_pos).
  Hint Immediate o2l_pos_equation_1 : eqns_explicit.
  Hint Immediate o2l_pos_equation_2 : eqns_explicit.

  MetaCoq Run (infer_equations app_pos).
  Hint Immediate app_pos_equation_1 : eqns_explicit.
  Hint Immediate app_pos_equation_2 : eqns_explicit.

  MetaCoq Run (infer_equations map_fst).
  Hint Immediate map_fst_equation_1 : eqns_explicit.
  Hint Immediate map_fst_equation_2 : eqns_explicit.

  Definition map_fst_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map_fst_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map_fst_equation_1_P : eqns_implicit.
  Definition map_fst_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map_fst_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map_fst_equation_2_P : eqns_implicit.
  Definition app_pos_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma app_pos_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate app_pos_equation_1_P : eqns_implicit.
  Definition app_pos_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma app_pos_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate app_pos_equation_2_P : eqns_implicit.
  Definition o2l_pos_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma o2l_pos_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate o2l_pos_equation_1_P : eqns_implicit.
  Definition o2l_pos_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma o2l_pos_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate o2l_pos_equation_2_P : eqns_implicit.
  Definition xkeys_eqn_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma xkeys_eqn)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate xkeys_eqn_P : eqns_implicit.

  Lemma map_fst_app:
    forall x y,
      map_fst (app_pos_A x y) = app_pos (map_fst x) (map_fst y).
  Proof.
    induction x;
    mirrorsolve.
  Qed.

  Hint Immediate map_fst_app : eqns_explicit.
  Definition map_fst_app_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma map_fst_app)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate map_fst_app_P : eqns_implicit.

  MetaCoq Run (infer_equations fst_pos_A).
  Hint Immediate fst_pos_A_equation_1 : eqns_explicit.
  Definition fst_pos_A_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fst_pos_A_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fst_pos_A_equation_1_P : eqns_implicit.

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":2, "hammer":0, "crush":0} *)
  Lemma xkeys_Node:
    forall (m1: tree A) o (m2: tree A) i,
    xkeys (Node m1 o m2) i =
      app_pos (xkeys m1 (xO i))
      (app_pos 
        (o2l_pos i o)
        (xkeys m2 (xI i))).
  Proof.
    induction o;
    mirrorsolve.
  Qed.

  Hint Immediate xkeys_Node : eqns_explicit.

  MetaCoq Run (infer_equations In_pos).
  Hint Immediate In_pos_equation_1 : eqns_explicit.
  Hint Immediate In_pos_equation_2 : eqns_explicit.

  Definition In_pos_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma In_pos_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate In_pos_equation_1_P : eqns_implicit.
  Definition In_pos_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma In_pos_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate In_pos_equation_2_P : eqns_implicit.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":2, "hammer":0, "crush":0} *)
  Lemma in_pos_map_fst_inv:
    forall (l: list (positive * A)) (p: positive),
      In_pos p (map_fst l) -> 
      ~ (forall a : A, ~ (In_pos_A (p, a) l)).
  Proof.
    induction l;
    mirrorsolve.
  Qed.

  Hint Immediate in_pos_map_fst_inv : eqns_explicit.
  Definition in_pos_map_fst_inv_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma in_pos_map_fst_inv)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate in_pos_map_fst_inv_P : eqns_implicit.

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":1, "ms":1, "hammer":0, "crush":0} *)
  Lemma in_xkeys:
    forall (m: tree A) (i k: positive),
    In_pos k (xkeys m i) ->
    ~ (forall j, ~ (k = prev (prev_append j i))).
  Proof.
    mirrorsolve.
    (* unfold xkeys; intros.
    apply (list_in_map_inv) in H. destruct H as ((j, v) & -> & H).
    exploit in_xelements; eauto. intros (k & P & Q). exists k; auto. *)
  Qed.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":4, "ms":4, "hammer":0, "crush":0} *)
  Lemma in_app_pos : 
    forall l r v, 
      In_pos v (app_pos l r) <-> In_pos v l \/ In_pos v r.
  Proof.
    induction l;
    induction r;
    mirrorsolve.
  Qed.

  Hint Immediate in_app_pos : eqns_explicit.
  Definition in_app_pos_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma in_app_pos)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate in_app_pos_P : eqns_implicit.

  Hint Immediate in_xkeys : eqns_explicit.
  Definition in_xkeys_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma in_xkeys)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate in_xkeys_P : eqns_implicit.

  MetaCoq Run (infer_equations NoDup_pos).
  Hint Immediate NoDup_pos_equation_1 : eqns_explicit.
  Hint Immediate NoDup_pos_equation_2 : eqns_explicit.
  Definition NoDup_pos_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma NoDup_pos_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate NoDup_pos_equation_1_P : eqns_implicit.
  Definition NoDup_pos_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma NoDup_pos_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate NoDup_pos_equation_2_P : eqns_implicit.

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":1, "hammer":0, "crush":0} *)
  Lemma NoDup_pos_app : 
    forall l r, 
      NoDup_pos l -> 
      NoDup_pos r -> 
      (forall x, (In_pos x l -> ~ In_pos x r) /\ (In_pos x r -> ~ In_pos x l)) -> 
      NoDup_pos (app_pos l r).
  Proof.
    induction l;
    mirrorsolve.
  Qed.

  Hint Immediate NoDup_pos_app : eqns_explicit.
  Definition NoDup_pos_app_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma NoDup_pos_app)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate NoDup_pos_app_P : eqns_implicit.


  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":3, "ms":2, "hammer":0, "crush":0} *)
  Lemma xelements_keys_norepet:
    forall (m: tree A) (i: positive),
    NoDup_pos (xkeys m i).
  Proof.
    induction m using nodes_ind;
    try (destruct o);
    mirrorsolve.

(*     
    intros A; induction m using tree_ind; intros.
  - constructor.
  - assert (NOTIN1: ~ In (prev i) (xkeys l (xO i))).
    { red; intros. exploit in_xkeys; eauto. intros (j & EQ).
      rewrite prev_append_prev in EQ. simpl in EQ. apply prev_append_inj in EQ. discriminate. }
    assert (NOTIN2: ~ In (prev i) (xkeys r (xI i))).
    { red; intros. exploit in_xkeys; eauto. intros (j & EQ).
      rewrite prev_append_prev in EQ. simpl in EQ. apply prev_append_inj in EQ. discriminate. }
    assert (DISJ: forall x, In x (xkeys l (xO i)) -> In x (xkeys r (xI i)) -> False).
    { intros. exploit in_xkeys. eexact H0. intros (j1 & EQ1).
      exploit in_xkeys. eexact H1. intros (j2 & EQ2).
      rewrite prev_append_prev in *. simpl in *. rewrite EQ2 in EQ1. apply prev_append_inj in EQ1. discriminate. }
    rewrite xkeys_Node. apply list_norepet_append. auto.
    destruct o; simpl; auto. constructor; auto.
    red; intros. red; intros; subst y. destruct o; simpl in H1.
    destruct H1. subst x. tauto. eauto. eauto. *)
  Admitted.

  Hint Immediate xelements_keys_norepet : eqns_explicit.
  Definition xelements_keys_norepet_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma xelements_keys_norepet)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate xelements_keys_norepet_P : eqns_implicit.

  (* Lemma xkeys_elements_spec : 
    forall m,  *)

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":2, "hammer":0, "crush":0} *)
  Theorem elements_keys_norepet:
    forall (m: tree A),
      NoDup_pos (map_fst (elements m)).
  Proof.
    induction m;
    mirrorsolve.
  Qed.

  Hint Immediate elements_keys_norepet : eqns_explicit.
  Definition elements_keys_norepet_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma elements_keys_norepet)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate elements_keys_norepet_P : eqns_implicit.

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":1, "hammer":0, "crush":0} *)
  Remark xelements_empty:
    forall (m: tree A) i, 
      (forall i, get i m = None) -> 
      xelements m i = nil.
  Proof.
    (* induction m;
    mirrorsolve.
    Restart. *)
    intros.
    assert (m = Empty) by (eapply extensionality_empty; eauto).
    mirrorsolve.
  Qed.

  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": True, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  (* Theorem elements_canonical_order':
    forall (A B: Type) (R: A -> B -> Prop) (m: t A) (n: t B),
    (forall i, option_rel R (get i m) (get i n)) ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      (elements m) (elements n).
  Proof.
    intros until n.
    change (elements m) with (xelements m xH). change (elements n) with (xelements n xH).
    generalize 1%positive. revert m n.
    induction m using tree_ind; [ | induction n using tree_ind]; intros until p; intros REL.
  - replace n with (@Empty B). constructor.
    apply extensionality; intros. specialize (REL i). simpl in *. inv REL; auto.
  - replace (Node l o r) with (@Empty A). constructor.
    apply extensionality; intros. specialize (REL i). simpl in *. inv REL; auto.
  - rewrite ! xelements_Node. repeat apply list_forall2_app.
    + apply IHm. intros. specialize (REL (xO i)). rewrite ! gNode in REL; auto.
    + specialize (REL xH). rewrite ! gNode in REL. inv REL; constructor; auto using list_forall2_nil.
    + apply IHm0. intros. specialize (REL (xI i)). rewrite ! gNode in REL; auto.
  Qed. *)

  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": True, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  (* Theorem elements_canonical_order:
    forall (A B: Type) (R: A -> B -> Prop) (m: t A) (n: t B),
    (forall i x, get i m = Some x -> exists y, get i n = Some y /\ R x y) ->
    (forall i y, get i n = Some y -> exists x, get i m = Some x /\ R x y) ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      (elements m) (elements n).
  Proof.
    intros. apply elements_canonical_order'.
    intros. destruct (get i m) as [x|] eqn:GM.
    exploit H; eauto. intros (y & P & Q). rewrite P; constructor; auto.
    destruct (get i n) as [y|] eqn:GN.
    exploit H0; eauto. intros (x & P & Q). congruence.
    constructor.
  Qed. *)

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":1, "ms":0, "hammer":0, "crush":0} *)
  Theorem elements_extensional:
    forall (m n: tree A),
    (forall i, get i m = get i n) ->
    elements m = elements n.
  Proof.
    (* mirrorsolve.
    Restart. *)
    intros.
    assert (n = m) by (eapply extensionality; eauto).
    mirrorsolve.
  Qed.

  Lemma app_pos_A_ass:
    forall x y z, 
      app_pos_A x (app_pos_A y z) = app_pos_A (app_pos_A x y) z.
  Proof.
    induction x;
    mirrorsolve.
  Qed.
  
  Lemma app_pos_ass:
    forall x y z, 
      app_pos x (app_pos y z) = app_pos (app_pos x y) z.
  Proof.
    induction x;
    mirrorsolve.
  Qed.

  Hint Immediate app_pos_A_ass : eqns_explicit.
  Hint Immediate app_pos_ass : eqns_explicit.
  Definition app_pos_A_ass_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma app_pos_A_ass)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate app_pos_A_ass_P : eqns_implicit.
  Definition app_pos_ass_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma app_pos_ass)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate app_pos_ass_P : eqns_implicit.


  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":4, "ms":1, "hammer":0, "crush":0} *)
  Lemma xelements_remove:
    forall v (m: tree A) i j,
    get i m = Some v ->
    ~ (forall l1 l2,
    ~ (xelements m j = app_pos_A l1 ((prev (prev_append i j), v) :: l2)
    /\ xelements (remove i m) j = app_pos_A l1 l2)).
  Proof.
    induction m using nodes_ind; intros.
    - mirrorsolve.
    - assert (REMOVE: remove i (Node m1 o m2) =
                      match i with
                      | xH => Node m1 None m2
                      | xO ii => Node (remove ii m1) o m2
                      | xI ii => Node m1 o (remove ii m2)
                      end).
      { destruct m1, o, m2, i; reflexivity. }
      rewrite gNode in H0. rewrite REMOVE. destruct i; rewrite ! xelements_Node.
      + specialize (IHm2 i (xI j)).
        mirrorsolve.
      + specialize (IHm1 i (xO j)).
        mirrorsolve.
      + mirrorsolve.
  Qed.

  Hint Immediate xelements_remove : eqns_explicit.
  Definition xelements_remove_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma xelements_remove)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate xelements_remove_P : eqns_implicit.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":2, "hammer":0, "crush":0} *)
  Lemma elements_xelements_nodes:
    forall m, 
      elements m = xelements m xH.
  Proof.
    induction m;
    mirrorsolve.
  Qed.

  Hint Immediate elements_xelements_nodes : eqns_explicit.
  Definition elements_xelements_nodes_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma elements_xelements_nodes)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate elements_xelements_nodes_P : eqns_implicit.


  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":1, "ms":0, "hammer":0, "crush":0} *)
  Theorem elements_remove:
    forall i v (m: tree A),
    get i m = Some v ->
    ~ (forall l1 l2, ~ (elements m = app_pos_A l1 ((i,v) :: l2) /\ elements (remove i m) = app_pos_A l1 l2)).
  Proof.
    intros.
    pose proof (xelements_remove v m i xH).
    mirrorsolve.
  Qed.

  MetaCoq Run (infer_equations list_pos_A_fold_left).
  Hint Immediate list_pos_A_fold_left_equation_1 : eqns_explicit.
  Hint Immediate list_pos_A_fold_left_equation_2 : eqns_explicit.

  Definition list_pos_A_fold_left_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma list_pos_A_fold_left_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate list_pos_A_fold_left_equation_1_P : eqns_implicit.
  Definition list_pos_A_fold_left_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma list_pos_A_fold_left_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate list_pos_A_fold_left_equation_2_P : eqns_implicit.

  MetaCoq Run (infer_equations snd_pos_A).
  Hint Immediate snd_pos_A_equation_1 : eqns_explicit.
  Definition snd_pos_A_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma snd_pos_A_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate snd_pos_A_equation_1_P : eqns_implicit.

(** ** Folding over a tree *)

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":8, "ms":8, "hammer":0, "crush":0} *)
  Lemma fold'_xelements':
    forall m i v l,
    list_pos_A_fold_left l (fold' i m v) =
    list_pos_A_fold_left (xelements' m i l) v.
  Proof.
    induction m;
    mirrorsolve.
  Qed.

  Hint Immediate fold'_xelements' : eqns_explicit.
  Definition fold'_xelements'_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold'_xelements')); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold'_xelements'_P : eqns_implicit.

  MetaCoq Run (infer_equations fold).
  Hint Immediate fold_equation_1 : eqns_explicit.
  Hint Immediate fold_equation_2 : eqns_explicit.

  Definition fold_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold_equation_1_P : eqns_implicit.
  Definition fold_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold_equation_2_P : eqns_implicit.


  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":2, "hammer":0, "crush":0} *)
  Theorem fold_spec:
    forall (v: B) (m: tree A),
    fold m v =
    list_pos_A_fold_left (elements m) v.
  Proof.
    induction m;
    mirrorsolve.
  Qed.

  Hint Immediate fold_spec : eqns_explicit.
  Definition fold_spec_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold_spec)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold_spec_P : eqns_implicit.

  MetaCoq Run (infer_equations list_A_fold_left).
  Hint Immediate list_A_fold_left_equation_1 : eqns_explicit.
  Hint Immediate list_A_fold_left_equation_2 : eqns_explicit.

  Definition list_A_fold_left_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma list_A_fold_left_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate list_A_fold_left_equation_1_P : eqns_implicit.
  Definition list_A_fold_left_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma list_A_fold_left_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate list_A_fold_left_equation_2_P : eqns_implicit.

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  Lemma fold1'_xelements':
    forall m i v l,
    list_A_fold_left l (fold1' m v) =
    list_A_fold_left (xelements' m i l) v.
  Proof.
    induction m;
    mirrorsolve.
  Qed.

  Hint Immediate fold1'_xelements' : eqns_explicit.
  Definition fold1'_xelements'_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold1'_xelements')); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold1'_xelements'_P : eqns_implicit.

  MetaCoq Run (infer_equations fold1).
  Hint Immediate fold1_equation_1 : eqns_explicit.
  Hint Immediate fold1_equation_2 : eqns_explicit.
  Definition fold1_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold1_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold1_equation_1_P : eqns_implicit.
  Definition fold1_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold1_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate fold1_equation_2_P : eqns_implicit.

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  Theorem fold1_spec:
    forall (v: B) (m: tree A),
    fold1 m v =
    list_A_fold_left (elements m) v.
  Proof.
    induction m;
    mirrorsolve.
  Qed.

(** Two induction principles over [fold]. *)

  (* Variables V A: Type.
  Variable f: A -> positive -> V -> A.
  Variable P: tree V -> A -> Type.
  Variable init: A.
  Variable m_final: tree V.

  Hypothesis H_base:
    forall m,
    (forall k, T.get k m = None) ->
    P m init.

  Hypothesis H_rec:
    forall m a k v,
    T.get k m = Some v -> T.get k m_final = Some v ->
    P (T.remove k m) a -> P m (f a k v).

  Let f' (p : T.elt * V) (a: A) := f a (fst p) (snd p).

  Let P' (l: list (T.elt * V)) (a: A) : Type :=
    forall m, (forall k v, In (k, v) l <-> T.get k m = Some v) -> P m a. *)

  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": True, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  (* Let H_base':
    P' nil init.
  Proof.
    intros m EQV. apply H_base.
    intros. destruct (T.get k m) as [v|] eqn:G; auto.
    apply EQV in G. contradiction.
  Qed. *)

  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": True, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  (* Let H_rec':
    forall k v l a,
    ~In k (List.map fst l) ->
    T.get k m_final = Some v ->
    P' l a ->
    P' ((k, v) :: l) (f a k v).
  Proof.
    unfold P'; intros k v l a NOTIN FINAL HR m EQV.
    set (m0 := T.remove k m).
    apply H_rec.
  - apply EQV. simpl; auto.
  - auto.
  - apply HR. intros k' v'. rewrite T.grspec. split; intros; destruct (T.elt_eq k' k).
    + subst k'. elim NOTIN. change k with (fst (k, v')). apply List.in_map; auto.
    + apply EQV. simpl; auto.
    + congruence.
    + apply EQV in H. simpl in H. intuition congruence.
  Qed. *)

  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": True, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  (* Lemma fold_ind_aux:
    forall l,
    (forall k v, In (k, v) l -> T.get k m_final = Some v) ->
    list_norepet (List.map fst l) ->
    P' l (List.fold_right f' init l).
  Proof.
    induction l as [ | [k v] l ]; simpl; intros FINAL NOREPET.
  - apply H_base'.
  - apply H_rec'.
    + inv NOREPET. auto.
    + apply FINAL. auto.
    + apply IHl. auto. inv NOREPET; auto.
  Defined. *)

  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": True, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  (* Theorem fold_ind:
    P m_final (T.fold f m_final init).
  Proof.
    intros.
    set (l' := List.rev (T.elements m_final)).
    assert (P' l' (List.fold_right f' init l')).
    { apply fold_ind_aux.
      intros. apply T.elements_complete. apply List.in_rev. auto.
      unfold l'; rewrite List.map_rev. apply list_norepet_rev. apply T.elements_keys_norepet. }
    unfold l', f' in X; rewrite fold_left_rev_right in X.
    rewrite T.fold_spec. apply X.
    intros; simpl. rewrite <- List.in_rev.
    split. apply T.elements_complete. apply T.elements_correct.
  Defined. *)

(* Hypothesis P_compat:
  forall m m' a,
  (forall x, T.get x m = T.get x m') ->
  P m a -> P m' a.

Hypothesis H_base:
  P (T.empty _) init.

Hypothesis H_rec:
  forall m a k v,
  T.get k m = None -> T.get k m_final = Some v -> P m a -> P (T.set k v m) (f a k v). *)

(*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": True, "goals":0, "ms":0, "hammer":0, "crush":0} *)
(* Theorem fold_rec:
  P m_final (T.fold f m_final init).
Proof.
  apply fold_ind. 
- intros. apply P_compat with (T.empty V); auto.
  + intros. rewrite T.gempty. auto.
- intros. apply P_compat with (T.set k v (T.remove k m)).
  + intros. rewrite T.gsspec, T.grspec. destruct (T.elt_eq x k); auto. congruence.
  + apply H_rec; auto. apply T.grs.
Qed. *)

(** A nonnegative measure over trees *)

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma cardinal_eqn:
    forall x, 
      cardinal x = length_pos_A (elements x).
  Proof.
    intros.
    exact eq_refl.
  Qed.

  MetaCoq Run (infer_equations length_pos_A).
  Hint Immediate length_pos_A_equation_1 : eqns_explicit.
  Hint Immediate length_pos_A_equation_2 : eqns_explicit.

  MetaCoq Run (infer_equations Nat.add).
  Hint Immediate add_equation_1 : eqns_explicit.
  Hint Immediate add_equation_2 : eqns_explicit.

  Definition length_pos_A_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma length_pos_A_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate length_pos_A_equation_1_P : eqns_implicit.
  Definition length_pos_A_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma length_pos_A_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate length_pos_A_equation_2_P : eqns_implicit.
  Definition add_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma add_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate add_equation_1_P : eqns_implicit.
  Definition add_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma add_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate add_equation_2_P : eqns_implicit.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":2, "hammer":0, "crush":0} *)
  Lemma app_pos_A_length:
    forall x y,
      length_pos_A (app_pos_A x y) = length_pos_A x + length_pos_A y.
  Proof.
    induction x;
    mirrorsolve.
  Qed.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma le_n_eqn:
    forall x, 
      (x <= x)%nat <-> True.
  Proof.
    intros.
    intuition econstructor.
  Qed.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma le_S_eqn:
    forall n m, 
      (n <= m) -> (n <= S m).
  Proof.
    intros.
    intuition econstructor.
    eauto.
  Qed.

  Hint Immediate le_n_eqn : eqns_explicit.
  Hint Immediate le_S_eqn : eqns_explicit.
  Definition le_n_eqn_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma le_n_eqn)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate le_n_eqn_P : eqns_implicit.
  Definition le_S_eqn_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma le_S_eqn)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate le_S_eqn_P : eqns_implicit.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma lt_eqn:
    forall x y, 
      (x < y <-> S x <= y)%nat.
  Proof.
    intros.
    eapply iff_refl.
  Qed.

  Hint Immediate lt_eqn : eqns_explicit.
  Definition lt_eqn_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma lt_eqn)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate lt_eqn_P : eqns_implicit.

  Hint Immediate cardinal_eqn : eqns_explicit.
  Definition cardinal_eqn_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma cardinal_eqn)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate cardinal_eqn_P : eqns_implicit.

  (* 
    pressburger arithmetic axioms
  *)

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":2, "hammer":0, "crush":0} *)
  Lemma pres_add_nonzero:
    forall x, 
      ~ (x + 1 = 0)%nat.
  Proof.
    induction x;
    mirrorsolve.
  Qed.

  Hint Immediate pres_add_nonzero : eqns_explicit.
  Definition pres_add_nonzero_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma pres_add_nonzero)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate pres_add_nonzero_P : eqns_implicit.


  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":4, "ms":4, "hammer":0, "crush":0} *)
  Lemma pres_add_inj:
    forall x y,
      x + 1 = y + 1 -> 
      x = y.
  Proof.
    induction x;
    induction y;
    mirrorsolve.
  Qed.

  Hint Immediate pres_add_inj : eqns_explicit.
  Definition pres_add_inj_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma pres_add_inj)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate pres_add_inj_P : eqns_implicit.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":2, "hammer":0, "crush":0} *)
  Lemma pres_add_zero:
    forall x, 
      x + 0 = x.
  Proof.
    induction x;
    mirrorsolve.
  Qed.

  Hint Immediate pres_add_zero : eqns_explicit.
  Definition pres_add_zero_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma pres_add_zero)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate pres_add_zero_P : eqns_implicit.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals":2, "ms":2, "hammer":0, "crush":0} *)
  Lemma pres_add_assoc:
    forall x y z, 
      x + (y + z) = (x + y) + z.
  Proof.
    induction x;
    mirrorsolve.
  Qed.

  Hint Immediate pres_add_assoc : eqns_explicit.
  Definition pres_add_assoc_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma pres_add_assoc)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
  Hint Immediate pres_add_assoc_P : eqns_implicit.

(*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
  Theorem cardinal_remove:
    forall m x y, 
      get x m = Some y -> 
      (cardinal (remove x m) < cardinal m)%nat.
  Proof.
    induction m.
    mirrorsolve.
  Admitted.

(*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":1, "ms":0, "hammer":0, "crush":0} *)
Theorem cardinal_set:
  forall x m y, 
    get x m = None -> 
    (cardinal m < cardinal (set x y m))%nat.
Proof.
Admitted.

Definition fold'_and_equation_1_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold'_and_equation_1)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
Hint Immediate fold'_and_equation_1_P : eqns_implicit.
Definition fold'_and_equation_2_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold'_and_equation_2)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
Hint Immediate fold'_and_equation_2_P : eqns_implicit.
Definition fold'_and_equation_3_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold'_and_equation_3)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
Hint Immediate fold'_and_equation_3_P : eqns_implicit.
Definition fold'_and_equation_4_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold'_and_equation_4)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
Hint Immediate fold'_and_equation_4_P : eqns_implicit.
Definition fold'_and_equation_5_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold'_and_equation_5)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
Hint Immediate fold'_and_equation_5_P : eqns_implicit.
Definition fold'_and_equation_6_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold'_and_equation_6)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
Hint Immediate fold'_and_equation_6_P : eqns_implicit.
Definition fold'_and_equation_7_P : interp_fm (sig := sig) (m := fm_model) (VEmp _ _) _ := ltac:(set (v := ltac:(conv_lemma fold'_and_equation_7)); eapply UnsoundAxioms.interp_true with (m := fm_model) (form := v)).
Hint Immediate fold'_and_equation_7_P : eqns_implicit.

Fixpoint fold'_poly {A B} (f: B -> positive -> A -> B)
                 (i: positive) (m: tree' A) (v: B) {struct m} : B :=
  match m with
  | Node001 r => fold'_poly f (xI i) r v
  | Node010 x => f v (prev i) x
  | Node011 x r => fold'_poly f (xI i) r (f v (prev i) x)
  | Node100 l => fold'_poly f (xO i) l v
  | Node101 l r => fold'_poly f (xI i) r (fold'_poly f (xO i) l v)
  | Node110 l x => f (fold'_poly f (xO i) l v) (prev i) x
  | Node111 l x r => fold'_poly f (xI i) r (f (fold'_poly f (xO i) l v) (prev i) x)
  end.

  Definition fold_poly {A B} (f: B -> positive -> A -> B) (m: tree A) (v: B) :=
   match m with Empty => v | Nodes m' => fold'_poly f xH m' v end.

  Lemma fold'_poly_inst: 
    forall m i b, 
      fold'_poly (fun b x a => b && f_pos_A_bool_sym x a)%bool i m b = (b && fold'_and i m)%bool.
  Proof.
    induction m; intros; simpl in *;
    try (now f_equal).
    - erewrite IHm. 
      destruct b; simpl;
      f_equal;
      trivial.
    - erewrite IHm1.
      erewrite IHm2.
      destruct b; 
      destruct (fold'_and i~0 m1);
      destruct (fold'_and i~1 m2);
      simpl; 
      trivial.
    - erewrite IHm.
      destruct b; simpl; trivial.
      destruct (fold'_and i~0 m);
      destruct (f_pos_A_bool_sym (prev i) a);
      simpl;
      trivial.
    - erewrite IHm1.
      erewrite IHm2.
      destruct b; 
      destruct (fold'_and i~0 m1);
      destruct (fold'_and i~1 m2);
      destruct (f_pos_A_bool_sym (prev i) a);
      simpl; 
      trivial.
  Qed.

  Lemma fold_poly_inst: 
    forall m b, 
      fold_poly (fun b x a => b && f_pos_A_bool_sym x a)%bool m b = fold_and m b.
  Proof.
    destruct m;
    intros;
    simpl;
    trivial.
    eapply fold'_poly_inst.
  Qed.

Lemma fold_poly_ind :
  forall {V X} f (P: tree V -> X -> Prop) init final 
  (H_base:
    P Empty init)
  (P_rec:
    forall m a k v,
      get k m = None -> 
      get k final = Some v -> 
      P m a -> 
      P (set k v m) (f a k v)), 
  P final (fold_poly f final init).
Admitted.


(** Forall and exists *)
  Lemma fold_and_spec:
    forall m b,
      fold_and m b = b <-> 
      (forall x a, get x m = Some a -> f_pos_A_bool_sym x a = b)%bool.
  Proof.
    intros.
    erewrite <- fold_poly_inst.
    apply fold_poly_ind.
    unfold fold_and.
    
  Lemma fold'_and_spec:
    forall m i,
      fold'_and i m = true <-> 
      (forall x a, get' x m = Some a -> f_pos_A_bool_sym x a = true).
  Proof.
    
    induction m;
    intros;
    simpl.
    - 
    2: {
      split; intros.
      destruct x; autorewrite with get' in *; try congruence.
    }
    split; intros.
    eapply IHm; eauto.
    destruct x.
    simpl in *.
    eapply H.
    autorewrite with get' in *.
    eapply IHm.
    Print
    specialize (H _ _ H0).
    eapply H.
    simpl in H0.
    autorewrite with get' in H0.
    autorewrite with get'.


    erewrite IHm.
    split; intros.
    - eapply H.
      destruct x; autorewrite with get' in *; intuition eauto.
    mirrorsolve.
(*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": True, "goals":0, "ms":0, "hammer":0, "crush":0} *)
Lemma for_all_correct:
  forall m,
  for_all m = true <-> (forall x a, get x m = Some a -> f_pos_A_bool_sym x a = true).
Proof.
  intros m0 f.
  unfold for_all. apply fold_rec; intros.
- (* Extensionality *)
  rewrite H0. split; intros. rewrite <- H in H2; auto. rewrite H in H2; auto.
- (* Base case *)
  split; intros. rewrite T.gempty in H0; congruence. auto.
- (* Inductive case *)
  split; intros.
  destruct (andb_prop _ _ H2). rewrite T.gsspec in H3. destruct (T.elt_eq x k).
  inv H3. auto.
  apply H1; auto.
  apply andb_true_intro. split.
  rewrite H1. intros. apply H2. rewrite T.gso; auto. congruence.
  apply H2. apply T.gss.
Qed.

Definition exists_ (m: T.t A) (f: T.elt -> A -> bool) : bool :=
  T.fold (fun b x a => b || f x a) m false.

(*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": True, "goals":0, "ms":0, "hammer":0, "crush":0} *)
Lemma exists_correct:
  forall m f,
  exists_ m f = true <-> (exists x a, T.get x m = Some a /\ f x a = true).
Proof.
  intros m0 f.
  unfold exists_. apply fold_rec; intros.
- (* Extensionality *)
  rewrite H0. split; intros (x0 & a0 & P & Q); exists x0; exists a0; split; auto; congruence.
- (* Base case *)
  split; intros. congruence. destruct H as (x & a & P & Q). rewrite T.gempty in P; congruence.
- (* Inductive case *)
  split; intros.
  destruct (orb_true_elim _ _ H2).
  rewrite H1 in e. destruct e as (x1 & a1 & P & Q).
  exists x1; exists a1; split; auto. rewrite T.gso; auto. congruence.
  exists k; exists v; split; auto. apply T.gss.
  destruct H2 as (x1 & a1 & P & Q). apply orb_true_intro.
  rewrite T.gsspec in P. destruct (T.elt_eq x1 k).
  inv P. right; auto.
  left. apply H1. exists x1; exists a1; auto.
Qed.

(*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": True, "goals":0, "ms":0, "hammer":0, "crush":0} *)
Remark exists_for_all:
  forall m f,
  exists_ m f = negb (for_all m (fun x a => negb (f x a))).
Proof.
  intros. unfold exists_, for_all. rewrite ! T.fold_spec.
  change false with (negb true). generalize (T.elements m) true.
  induction l; simpl; intros.
  auto.
  rewrite <- IHl. f_equal.
  destruct b; destruct (f (fst a) (snd a)); reflexivity.
Qed.

(*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": True, "goals":0, "ms":0, "hammer":0, "crush":0} *)
Remark for_all_exists:
  forall m f,
  for_all m f = negb (exists_ m (fun x a => negb (f x a))).
Proof.
  intros. unfold exists_, for_all. rewrite ! T.fold_spec.
  change true with (negb false). generalize (T.elements m) false.
  induction l; simpl; intros.
  auto.
  rewrite <- IHl. f_equal.
  destruct b; destruct (f (fst a) (snd a)); reflexivity.
Qed.

(*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": True, "goals":0, "ms":0, "hammer":0, "crush":0} *)
Lemma for_all_false:
  forall m f,
  for_all m f = false <-> (exists x a, T.get x m = Some a /\ f x a = false).
Proof.
  intros. rewrite for_all_exists.
  rewrite negb_false_iff. rewrite exists_correct.
  split; intros (x & a & P & Q); exists x; exists a; split; auto.
  rewrite negb_true_iff in Q. auto.
  rewrite Q; auto.
Qed.

(*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": True, "goals":0, "ms":0, "hammer":0, "crush":0} *)
Lemma exists_false:
  forall m f,
  exists_ m f = false <-> (forall x a, T.get x m = Some a -> f x a = false).
Proof.
  intros. rewrite exists_for_all.
  rewrite negb_false_iff. rewrite for_all_correct.
  split; intros. apply H in H0. rewrite negb_true_iff in H0. auto. rewrite H; auto.
Qed.

End FORALL_EXISTS.

(** More about [beq] *)

Section BOOLEAN_EQUALITY.

Variable A: Type.
Variable beqA: A -> A -> bool.

(*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
Theorem beq_false:
  forall m1 m2,
  T.beq beqA m1 m2 = false <->
  exists x, match T.get x m1, T.get x m2 with
            | None, None => False
            | Some a1, Some a2 => beqA a1 a2 = false
            | _, _ => True
            end.
Proof.
  intros; split; intros.
- (* beq = false -> existence *)
  set (p1 := fun x a1 => match T.get x m2 with None => false | Some a2 => beqA a1 a2 end).
  set (p2 := fun x a2 => match T.get x m1 with None => false | Some a1 => beqA a1 a2 end).
  destruct (for_all m1 p1) eqn:F1; [destruct (for_all m2 p2) eqn:F2 | idtac].
  + cut (T.beq beqA m1 m2 = true). congruence.
    rewrite for_all_correct in *. rewrite T.beq_correct; intros.
    destruct (T.get x m1) as [a1|] eqn:X1.
    generalize (F1 _ _ X1). unfold p1. destruct (T.get x m2); congruence.
    destruct (T.get x m2) as [a2|] eqn:X2; auto.
    generalize (F2 _ _ X2). unfold p2. rewrite X1. congruence.
  + rewrite for_all_false in F2. destruct F2 as (x & a & P & Q).
    exists x. rewrite P. unfold p2 in Q. destruct (T.get x m1); auto.
  + rewrite for_all_false in F1. destruct F1 as (x & a & P & Q).
    exists x. rewrite P. unfold p1 in Q. destruct (T.get x m2); auto.
- (* existence -> beq = false *)
  destruct H as [x P].
  destruct (T.beq beqA m1 m2) eqn:E; auto.
  rewrite T.beq_correct in E.
  generalize (E x). destruct (T.get x m1); destruct (T.get x m2); tauto || congruence.
Qed.

End BOOLEAN_EQUALITY.

(** Extensional equality between trees *)

Section EXTENSIONAL_EQUALITY.

Variable A: Type.
Variable eqA: A -> A -> Prop.
Hypothesis eqAeq: Equivalence eqA.

Definition Equal (m1 m2: T.t A) : Prop :=
  forall x, match T.get x m1, T.get x m2 with
                | None, None => True
                | Some a1, Some a2 => a1 === a2
                | _, _ => False
            end.

(*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
Lemma Equal_refl: forall m, Equal m m.
Proof.
  intros; red; intros. destruct (T.get x m); auto. reflexivity.
Qed.

(*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
Lemma Equal_sym: forall m1 m2, Equal m1 m2 -> Equal m2 m1.
Proof.
  intros; red; intros. generalize (H x). destruct (T.get x m1); destruct (T.get x m2); auto. intros; symmetry; auto.
Qed.

(*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
Lemma Equal_trans: forall m1 m2 m3, Equal m1 m2 -> Equal m2 m3 -> Equal m1 m3.
Proof.
  intros; red; intros. generalize (H x) (H0 x).
  destruct (T.get x m1); destruct (T.get x m2); try tauto;
  destruct (T.get x m3); try tauto.
  intros. transitivity a0; auto.
Qed.

Global Instance Equal_Equivalence : Equivalence Equal := {
  Equivalence_Reflexive := Equal_refl;
  Equivalence_Symmetric := Equal_sym;
  Equivalence_Transitive := Equal_trans
}.

Hypothesis eqAdec: EqDec A eqA.

Program Definition Equal_dec (m1 m2: T.t A) : { m1 === m2 } + { m1 =/= m2 } :=
  match T.beq (fun a1 a2 => proj_sumbool (a1 == a2)) m1 m2 with
  | true => left _
  | false => right _
  end.
Next Obligation.
  rename Heq_anonymous into B.
  symmetry in B. rewrite T.beq_correct in B.
  red; intros. generalize (B x).
  destruct (T.get x m1); destruct (T.get x m2); auto.
  intros. eapply proj_sumbool_true; eauto.
Qed.
Next Obligation.
  assert (T.beq (fun a1 a2 => proj_sumbool (a1 == a2)) m1 m2 = true).
  apply T.beq_correct; intros.
  generalize (H x).
  destruct (T.get x m1); destruct (T.get x m2); try tauto.
  intros. apply proj_sumbool_is_true; auto.
  unfold equiv, complement in H0. congruence.
Qed.

Global Instance Equal_EqDec : EqDec (T.t A) Equal := Equal_dec.

End EXTENSIONAL_EQUALITY.

(** Creating a tree from a list of (key, value) pairs. *)

Section OF_LIST.

Variable A: Type.

Let f := fun (m: T.t A) (k_v: T.elt * A) => T.set (fst k_v) (snd k_v) m.

Definition of_list (l: list (T.elt * A)) : T.t A :=
  List.fold_left f l (T.empty _).

(*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
Lemma in_of_list:
  forall l k v, T.get k (of_list l) = Some v -> In (k, v) l.
Proof.
  assert (REC: forall k v l m,
           T.get k (fold_left f l m) = Some v -> In (k, v) l \/ T.get k m = Some v).
  { induction l as [ | [k1 v1] l]; simpl; intros.
  - tauto.
  - apply IHl in H. unfold f in H. simpl in H. rewrite T.gsspec in H.
    destruct H; auto.
    destruct (T.elt_eq k k1). inv H. auto. auto.
  }
  intros. apply REC in H. rewrite T.gempty in H. intuition congruence.
Qed.

(*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
Lemma of_list_dom:
  forall l k, In k (map fst l) -> exists v, T.get k (of_list l) = Some v.
Proof.
  assert (REC: forall k l m,
            In k (map fst l) \/ (exists v, T.get k m = Some v) ->
            exists v, T.get k (fold_left f l m) = Some v).
  { induction l as [ | [k1 v1] l]; simpl; intros.
  - tauto.
  - apply IHl. unfold f; rewrite T.gsspec. simpl. destruct (T.elt_eq k k1).
    right; econstructor; eauto.
    intuition congruence.
  }
  intros. apply REC. auto.
Qed.

(*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
Remark of_list_unchanged:
  forall k l m, ~In k (map fst l) -> T.get k (List.fold_left f l m) = T.get k m.
Proof.
  induction l as [ | [k1 v1] l]; simpl; intros.
- auto.
- rewrite IHl by tauto. unfold f; apply T.gso; intuition auto.
Qed.

(*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
Lemma of_list_unique:
  forall k v l1 l2,
  ~In k (map fst l2) -> T.get k (of_list (l1 ++ (k, v) :: l2)) = Some v.
Proof.
  intros. unfold of_list. rewrite fold_left_app. simpl.
  rewrite of_list_unchanged by auto. unfold f; apply T.gss.
Qed.

(*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
Lemma of_list_norepet:
  forall l k v, list_norepet (map fst l) -> In (k, v) l -> T.get k (of_list l) = Some v.
Proof.
  assert (REC: forall k v l m,
            list_norepet (map fst l) ->
            In (k, v) l ->
            T.get k (fold_left f l m) = Some v).
  { induction l as [ | [k1 v1] l]; simpl; intros.
    contradiction.
    inv H. destruct H0.
    inv H. rewrite of_list_unchanged by auto. apply T.gss.
    apply IHl; auto.
  }
  intros; apply REC; auto.
Qed.

(*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals":0, "ms":0, "hammer":0, "crush":0} *)
Lemma of_list_elements:
  forall m k, T.get k (of_list (T.elements m)) = T.get k m.
Proof.
  intros. destruct (T.get k m) as [v|] eqn:M.
- apply of_list_norepet. apply T.elements_keys_norepet. apply T.elements_correct; auto.
- destruct (T.get k (of_list (T.elements m))) as [v|] eqn:M'; auto.
  apply in_of_list in M'. apply T.elements_complete in M'. congruence.
Qed.

End OF_LIST.

(*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": True, "goals":0, "ms":0, "hammer":0, "crush":0} *)
Lemma of_list_related:
  forall (A B: Type) (R: A -> B -> Prop) k l1 l2,
  list_forall2 (fun ka kb => fst ka = fst kb /\ R (snd ka) (snd kb)) l1 l2 ->
  option_rel R (T.get k (of_list l1)) (T.get k (of_list l2)).
Proof.
  intros until k. unfold of_list.
  set (R' := fun ka kb => fst ka = fst kb /\ R (snd ka) (snd kb)).
  set (fa := fun (m : T.t A) (k_v : T.elt * A) => T.set (fst k_v) (snd k_v) m).
  set (fb := fun (m : T.t B) (k_v : T.elt * B) => T.set (fst k_v) (snd k_v) m).
  assert (REC: forall l1 l2, list_forall2 R' l1 l2 ->
               forall m1 m2, option_rel R (T.get k m1) (T.get k m2) ->
               option_rel R (T.get k (fold_left fa l1 m1)) (T.get k (fold_left fb l2 m2))).
  { induction 1; intros; simpl.
  - auto.
  - apply IHlist_forall2. unfold fa, fb. rewrite ! T.gsspec.
    destruct H as [E F]. rewrite E. destruct (T.elt_eq k (fst b1)).
    constructor; auto.
    auto. }
  intros. apply REC; auto. rewrite ! T.gempty. constructor.
Qed.

End Tree_Properties.

Module PTree_Properties := Tree_Properties(PTree).

(** * Useful notations *)

Notation "a ! b" := (PTree.get b a) (at level 1).
Notation "a !! b" := (PMap.get b a) (at level 1).

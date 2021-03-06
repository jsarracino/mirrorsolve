From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.

Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.

Import ListNotations.
Import HListNotations.
(* 
From SMTCoq Require Import SMTCoq. *)

Set Universe Polymorphism.
Section BFOL.
  Inductive sorts: Set :=
  | BoolSort.

  Scheme Equality for sorts.
  Set Universe Polymorphism.

  Inductive funs: arity sorts -> sorts -> Type :=
  | BLit: forall (b: bool), funs [] BoolSort
  | BAnd: funs [BoolSort; BoolSort] BoolSort
  | BOr: funs [BoolSort; BoolSort] BoolSort
  | BNot: funs [BoolSort] BoolSort
  | BImpl: funs [BoolSort; BoolSort] BoolSort.

  Inductive rels: arity sorts -> Type :=.

  Definition sig: signature :=
    {| sig_sorts := sorts;
      sig_funs := funs;
      sig_rels := rels |}.

  Definition fm ctx := FirstOrder.fm sig ctx.
  Definition tm ctx := FirstOrder.tm sig ctx.

  Definition mod_sorts (s: sig_sorts sig) : Type :=
    match s with
    | BoolSort => bool
    end.

  Local Open Scope bool_scope.

  Obligation Tactic := idtac.
  Equations 
    mod_fns params ret (f: sig_funs sig params ret) (args: HList.t mod_sorts params) 
    : mod_sorts ret :=
    { mod_fns _ _ (BLit b) hnil := b;
      mod_fns _ _ BAnd (x ::: y ::: hnil) := x && y;
      mod_fns _ _ BOr (x ::: y ::: hnil) := x || y;
      mod_fns _ _ BImpl (x ::: y ::: hnil) := implb x y;
      mod_fns _ _ BNot (x ::: hnil) := negb x
    }.

  Definition mod_rels params
    (args: sig_rels sig params)
    (env: HList.t mod_sorts params) : Prop :=
    match args with
    end.

  Program Definition fm_model : model sig := {|
    FirstOrder.mod_sorts := mod_sorts;
    FirstOrder.mod_fns := mod_fns;
    FirstOrder.mod_rels := mod_rels;
  |}.


  Lemma b_interp_subst b: 
    forall c v, 
      b = interp_tm (c := c) (sig := sig) (m := fm_model) v (TFun sig (BLit b) hnil).
  Proof.
    intros.
    vm_compute; reflexivity.
  Qed.

End BFOL.


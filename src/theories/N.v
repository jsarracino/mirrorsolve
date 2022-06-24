From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.

Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.

Import ListNotations.
Import HListNotations.

Require Import Coq.ZArith.BinInt.
Set Universe Polymorphism.

Section NFOL.
  Inductive sorts: Set :=
  | NS
  | BS.

  Scheme Equality for sorts.

  Inductive funs: arity sorts -> sorts -> Type :=
  | NLit: forall (n: nat), funs [] NS
  | BLit: forall (b: bool), funs [] BS
  (* | Sub: funs [NS; NS] NS *)
  | Plus: funs [NS; NS] NS
  | Mul: funs [NS; NS] NS
  | Div: funs [NS; NS] NS
  | Mod: funs [NS; NS] NS
  | Lte: funs [NS; NS] BS
  | Lt: funs [NS; NS] BS
  | Gte: funs [NS; NS] BS
  | Gt: funs [NS; NS] BS.

  Inductive rels: arity sorts -> Type :=.

  Definition sig: signature :=
    {| sig_sorts := sorts;
      sig_funs := funs;
      sig_rels := rels |}.

  Definition fm ctx := FirstOrder.fm sig ctx.
  Definition tm ctx := FirstOrder.tm sig ctx.

  Definition mod_sorts (s: sig_sorts sig) : Type :=
    match s with
    | NS => nat
    | BS => bool
    end.

  Obligation Tactic := idtac.
  Equations 
    mod_fns params ret (f: sig_funs sig params ret) (args: HList.t mod_sorts params) 
    : mod_sorts ret :=
    { mod_fns _ _ (BLit b) _ := b;
      mod_fns _ _ (NLit n) _ := n;
      (* mod_fns _ _ Sub (l ::: r ::: _) := Nat.sub l r; *)
      mod_fns _ _ Plus (l ::: r ::: _) := Nat.add l r;
      mod_fns _ _ Mul (l ::: r ::: _) := Nat.mul l r;
      mod_fns _ _ Div (l ::: r ::: _) := Nat.div l r;
      mod_fns _ _ Mod (l ::: r ::: _) := Nat.modulo l r;
      mod_fns _ _ Lte (l ::: r ::: _) := Nat.leb l r;
      mod_fns _ _ Lt (l ::: r ::: _) := Nat.ltb l r;
      mod_fns _ _ Gte (l ::: r ::: _) := Nat.leb r l;
      mod_fns _ _ Gt (l ::: r ::: _) := Nat.ltb l r;
    }.

  Definition mod_rels params
    (args: sig_rels sig params)
    (env: HList.t mod_sorts params) : Prop :=
    match args with
    end.

  Definition fm_model : model sig := {|
    FirstOrder.mod_sorts := mod_sorts;
    FirstOrder.mod_fns := mod_fns;
    FirstOrder.mod_rels := mod_rels;
  |}.

End NFOL.
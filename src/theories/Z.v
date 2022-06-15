From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.

Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.

Import ListNotations.
Import HListNotations.

Require Import Coq.ZArith.BinInt.

Section ZFOL.
  Inductive sorts: Set :=
  | ZS
  | BS.

  Scheme Equality for sorts.

  Inductive funs: arity sorts -> sorts -> Type :=
  | ZLit: forall (z: Z), funs [] ZS
  | BLit: forall (b: bool), funs [] BS
  | Neg: funs [ZS] ZS
  | Sub: funs [ZS; ZS] ZS
  | Plus: funs [ZS; ZS] ZS
  | Mul: funs [ZS; ZS] ZS
  | Div: funs [ZS; ZS] ZS
  | Mod: funs [ZS; ZS] ZS
  | Abs: funs [ZS] ZS
  | Lte: funs [ZS; ZS] BS
  | Lt: funs [ZS; ZS] BS
  | Gte: funs [ZS; ZS] BS
  | Gt: funs [ZS; ZS] BS.


  Inductive rels: arity sorts -> Type :=.

  Definition sig: signature :=
    {| sig_sorts := sorts;
      sig_funs := funs;
      sig_rels := rels |}.

  Definition fm ctx := FirstOrder.fm sig ctx.
  Definition tm ctx := FirstOrder.tm sig ctx.

  Definition mod_sorts (s: sig_sorts sig) : Type :=
    match s with
    | ZS => Z
    | BS => bool
    end.

  Obligation Tactic := idtac.
  Equations 
    mod_fns params ret (f: sig_funs sig params ret) (args: HList.t mod_sorts params) 
    : mod_sorts ret :=
    { mod_fns _ _ (BLit b) _ := b;
      mod_fns _ _ (ZLit z) _ := z;
      mod_fns _ _ Neg (x ::: _) := Z.opp x;
      mod_fns _ _ Sub (l ::: r ::: _) := Z.sub l r;
      mod_fns _ _ Plus (l ::: r ::: _) := Z.add l r;
      mod_fns _ _ Mul (l ::: r ::: _) := Z.mul l r;
      mod_fns _ _ Div (l ::: r ::: _) := Z.div l r;
      mod_fns _ _ Mod (l ::: r ::: _) := Z.modulo l r;
      mod_fns _ _ Abs (x ::: _) := Z.abs x;
      mod_fns _ _ Lte (l ::: r ::: _) := Z.leb l r;
      mod_fns _ _ Lt (l ::: r ::: _) := Z.ltb l r;
      mod_fns _ _ Gte (l ::: r ::: _) := Z.geb l r;
      mod_fns _ _ Gt (l ::: r ::: _) := Z.gtb l r;
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


End ZFOL.
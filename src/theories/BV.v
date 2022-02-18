From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.

Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.

Import ListNotations.
Import HListNotations.

Require Import SMTCoq.SMTCoq.
Set Universe Polymorphism.

Import BVList.BITVECTOR_LIST.

Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.

Section BVFOL.
  Inductive sorts: Set :=
  | BS
  | BV: forall (width: N), sorts.

  Scheme Equality for sorts.

  (*  [[(concat s t)]] := λx:[0, n+m). if (x < m) then [[t]](x) else [[s]](x - m)
   where
   s and t are terms of sort (_ BitVec n) and (_ BitVec m), respectively,
   0 < n, 0 < m.

   - Function symbols for extraction

   [[((_ extract i j) s))]] := λx:[0, i-j+1). [[s]](j + x)
   where s is of sort (_ BitVec l), 0 ≤ j ≤ i < l.
   
   *)

  Inductive funs: arity sorts -> sorts -> Type :=
  | BVLit: forall (n: N) (bv: bitvector n), funs [] (BV n)
  | BLit: forall (b: bool), funs [] BS
  | BVCat: forall (n m: N), funs [(BV n); (BV m)] (BV (n + m))
  | BVExtr: forall (i n m: N), funs [BV m] (BV n).


  Inductive rels: arity sorts -> Type :=.

  Definition sig: signature :=
    {| sig_sorts := sorts;
      sig_funs := funs;
      sig_rels := rels |}.

  Definition fm ctx := FirstOrder.fm sig ctx.
  Definition tm ctx := FirstOrder.tm sig ctx.

  Definition mod_sorts (s: sig_sorts sig) : Type :=
    match s with
    | BV w => bitvector w
    | BS => bool
    end.

  Obligation Tactic := idtac.
  Equations 
    mod_fns params ret (f: sig_funs sig params ret) (args: HList.t mod_sorts params) 
    : mod_sorts ret :=
    { mod_fns _ _ (BVLit w bv) _ := bv;
      mod_fns _ _ (BLit b) _ := b;
      mod_fns _ _ (BVCat n m) (l ::: r ::: _) := bv_concat l r;
      mod_fns _ _ (BVExtr i n m) (x ::: _) := bv_extr i n x;
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

End BVFOL.
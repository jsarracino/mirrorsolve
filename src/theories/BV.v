From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.

Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.

Import ListNotations.
Import HListNotations.

(* Require Import SMTCoq.SMTCoq.
Set Universe Polymorphism.

Import BVList.BITVECTOR_LIST. *)

Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.

(* A definition of bitvectors using SMTCoq's BV representation  *)

Section BVFOL.

  (* TODO: update smtcoq to coq 8.16, replace axiom with actual smtcoq functions *)
  Axiom (bitvector: N -> Type).
  Axiom (bv_concat: forall {n m}, bitvector n -> bitvector m -> bitvector (n + m)).
  Axiom (bv_extr: forall {n} hi lo, bitvector n -> bitvector (N.min (1 + hi) n - lo)).

  Axiom (MkBitvector : forall (l: list bool), bitvector (N.of_nat (length l))).
  
  Inductive sorts: Set :=
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
  | BVCat: forall (n m: N), funs [(BV n); (BV m)] (BV (n + m))
  | BVExtr: forall (n hi lo: N), funs [BV n] (BV (N.min (1 + hi) n - lo)).

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
    end.

  Definition comp_eq_N {m n: N} (opaque_eq: m = n) : m = n :=
    match N.eq_dec m n with
    | left transparent_eq => transparent_eq
    | right _ => opaque_eq
    end.

  Local Obligation Tactic := intros.
  Equations 
    mod_fns params ret (f: sig_funs sig params ret) (args: HList.t mod_sorts params) 
    : mod_sorts ret :=
    { mod_fns _ _ (BVLit w bv) _ := bv;
      (* SMTLib flips concatenation, we use a transparent rewrite to avoid mucking up the term *)
      mod_fns _ _ (BVCat n m) (l ::: r ::: _) := 
        eq_rect_r _ (bv_concat r l) (comp_eq_N (N.add_comm n m));
      mod_fns _ _ (BVExtr n hi lo) (x ::: _) := bv_extr hi _ x;
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

Register BV as ms.bv.smt_bv.

Register BVLit as ms.bv.f_lit.
Register BVCat as ms.bv.f_cat.
Register BVExtr as ms.bv.f_extr.

Register MkBitvector as ms.bv.smt_bv_ctor.
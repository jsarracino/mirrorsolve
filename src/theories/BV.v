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

Require Import Coq.micromega.Lia.

(* A definition of bitvectors using SMTCoq's BV representation  *)

Definition bitvector (w: N) := { bv: list bool | N.of_nat (length bv) = w }.
Program Definition bv_cons {n} (b: bool) (bv: bitvector n) : bitvector (n + 1) := 
  b :: bv.
Next Obligation.
  destruct bv.
  simpl in *.
  lia.
Defined.

Program Definition bv_nil : bitvector 0 := @nil bool.
Notation "( x ; y )" := (exist _ x y) (at level 0, format "( x ; '/ ' y )").

Local Obligation Tactic := intros.
Program Definition bv_concat {n m} (x: bitvector n) (y: bitvector m) : bitvector (n + m) := List.app y x.
Next Obligation.
  simpl.
  destruct x;
  destruct y.
  simpl in *.
  erewrite app_length.
  lia.
Defined.

Program Definition bv_extr {n} (hi lo: N) (x: bitvector n) : bitvector (N.min (1 + hi)%N n - lo) := 
  List.skipn (N.to_nat lo) (List.firstn (1 + N.to_nat hi) x).
Next Obligation.
  intros.
  destruct x.
  simpl proj1_sig.
  erewrite skipn_length.
  erewrite firstn_length.
  lia.
Defined.

Program Definition MkBitvector (l: list bool) : bitvector (N.of_nat (length l)) := l.
Next Obligation.
  exact eq_refl.
Defined.

Definition bv_bits {n} (x: bitvector n) := proj1_sig x.
Definition bv_wf {n} (x: bitvector n) := proj2_sig x.

Section BVFOL.
  
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
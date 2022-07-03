(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
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

(** This file collects a number of definitions and theorems that are
    used throughout the development.  It complements the Coq standard
    library. *)

Require Export String.
Require Export ZArith.
Require Export Znumtheory.
Require Export List.
Require Export Bool.
Require Export Lia.

(** * Useful tactics *)

Ltac inv H := inversion H; clear H; subst.

Ltac predSpec pred predspec x y :=
  generalize (predspec x y); case (pred x y); intro.

Ltac caseEq name :=
  generalize (eq_refl name); pattern name at -1 in |- *; case name.

Ltac destructEq name :=
  destruct name eqn:?.

Ltac decEq :=
  match goal with
  | [ |- _ = _ ] => f_equal
  | [ |- (?X ?A <> ?X ?B) ] =>
      cut (A <> B); [intro; congruence | try discriminate]
  end.

Ltac byContradiction := exfalso.

Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof. auto. Qed.

Ltac exploit x :=
    refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _ _) _)
  || refine (modusponens _ _ (x _ _ _) _)
  || refine (modusponens _ _ (x _ _) _)
  || refine (modusponens _ _ (x _) _).

(** * Definitions and theorems over the type [positive] *)

Definition peq: forall (x y: positive), {x = y} + {x <> y} := Pos.eq_dec.
Global Opaque peq.

Lemma peq_true:
  forall (A: Type) (x: positive) (a b: A), (if peq x x then a else b) = a.
Proof.
  intros. case (peq x x); intros.
  auto.
  elim n; auto.
Qed.

Lemma peq_false:
  forall (A: Type) (x y: positive) (a b: A), x <> y -> (if peq x y then a else b) = b.
Proof.
  intros. case (peq x y); intros.
  elim H; auto.
  auto.
Qed.

Definition Plt: positive -> positive -> Prop := Pos.lt.

Lemma Plt_ne:
  forall (x y: positive), Plt x y -> x <> y.
Proof.
  unfold Plt; intros. red; intro. subst y. eelim Pos.lt_irrefl; eauto.
Qed.
Global Hint Resolve Plt_ne: coqlib.

Lemma Plt_trans:
  forall (x y z: positive), Plt x y -> Plt y z -> Plt x z.
Proof (Pos.lt_trans).

Lemma Plt_succ:
  forall (x: positive), Plt x (Pos.succ x).
Proof.
  unfold Plt; intros. apply Pos.lt_succ_r. apply Pos.le_refl.
Qed.
Global Hint Resolve Plt_succ: coqlib.

Lemma Plt_trans_succ:
  forall (x y: positive), Plt x y -> Plt x (Pos.succ y).
Proof.
  intros. apply Plt_trans with y. assumption. apply Plt_succ.
Qed.
Global Hint Resolve Plt_succ: coqlib.

Lemma Plt_succ_inv:
  forall (x y: positive), Plt x (Pos.succ y) -> Plt x y \/ x = y.
Proof.
  unfold Plt; intros. rewrite Pos.lt_succ_r in H.
  apply Pos.le_lteq; auto.
Qed.

Definition plt (x y: positive) : {Plt x y} + {~ Plt x y}.
Proof.
  unfold Plt, Pos.lt; intros. destruct (Pos.compare x y).
  - right; congruence.
  - left; auto.
  - right; congruence.
Defined.
Global Opaque plt.

Definition Ple: positive -> positive -> Prop := Pos.le.

Lemma Ple_refl: forall (p: positive), Ple p p.
Proof (Pos.le_refl).

Lemma Ple_trans: forall (p q r: positive), Ple p q -> Ple q r -> Ple p r.
Proof (Pos.le_trans).

Lemma Plt_Ple: forall (p q: positive), Plt p q -> Ple p q.
Proof (Pos.lt_le_incl).

Lemma Ple_succ: forall (p: positive), Ple p (Pos.succ p).
Proof.
  intros. apply Plt_Ple. apply Plt_succ.
Qed.

Lemma Plt_Ple_trans:
  forall (p q r: positive), Plt p q -> Ple q r -> Plt p r.
Proof (Pos.lt_le_trans).

Lemma Plt_strict: forall p, ~ Plt p p.
Proof (Pos.lt_irrefl).

Global Hint Resolve Ple_refl Plt_Ple Ple_succ Plt_strict: coqlib.

Ltac extlia := unfold Plt, Ple in *; lia.

(** Peano recursion over positive numbers. *)

Section POSITIVE_ITERATION.

Lemma Plt_wf: well_founded Plt.
Proof.
  apply well_founded_lt_compat with Pos.to_nat.
  intros. apply nat_of_P_lt_Lt_compare_morphism. exact H.
Qed.

Variable A: Type.
Variable v1: A.
Variable f: positive -> A -> A.

Lemma Ppred_Plt:
  forall x, x <> xH -> Plt (Pos.pred x) x.
Proof.
  intros. elim (Pos.succ_pred_or x); intro. contradiction.
  set (y := Pos.pred x) in *. rewrite <- H0. apply Plt_succ.
Qed.

Let iter (x: positive) (P: forall y, Plt y x -> A) : A :=
  match peq x xH with
  | left EQ => v1
  | right NOTEQ => f (Pos.pred x) (P (Pos.pred x) (Ppred_Plt x NOTEQ))
  end.

Definition positive_rec : positive -> A :=
  Fix Plt_wf (fun _ => A) iter.

Lemma unroll_positive_rec:
  forall x,
  positive_rec x = iter x (fun y _ => positive_rec y).
Proof.
  unfold positive_rec. apply (Fix_eq Plt_wf (fun _ => A) iter).
  intros. unfold iter. case (peq x 1); intro. auto. decEq. apply H.
Qed.

Lemma positive_rec_base:
  positive_rec 1%positive = v1.
Proof.
  rewrite unroll_positive_rec. unfold iter. case (peq 1 1); intro.
  auto. elim n; auto.
Qed.

Lemma positive_rec_succ:
  forall x, positive_rec (Pos.succ x) = f x (positive_rec x).
Proof.
  intro. rewrite unroll_positive_rec. unfold iter.
  case (peq (Pos.succ x) 1); intro.
  destruct x; simpl in e; discriminate.
  rewrite Pos.pred_succ. auto.
Qed.

Lemma positive_Peano_ind:
  forall (P: positive -> Prop),
  P xH ->
  (forall x, P x -> P (Pos.succ x)) ->
  forall x, P x.
Proof.
  intros.
  apply (well_founded_ind Plt_wf P).
  intros.
  case (peq x0 xH); intro.
  subst x0; auto.
  elim (Pos.succ_pred_or x0); intro. contradiction. rewrite <- H2.
  apply H0. apply H1. apply Ppred_Plt. auto.
Qed.

End POSITIVE_ITERATION.

(** * Definitions and theorems over the type [Z] *)

Definition zeq: forall (x y: Z), {x = y} + {x <> y} := Z.eq_dec.

Lemma zeq_true:
  forall (A: Type) (x: Z) (a b: A), (if zeq x x then a else b) = a.
Proof.
  intros. case (zeq x x); intros.
  auto.
  elim n; auto.
Qed.

Lemma zeq_false:
  forall (A: Type) (x y: Z) (a b: A), x <> y -> (if zeq x y then a else b) = b.
Proof.
  intros. case (zeq x y); intros.
  elim H; auto.
  auto.
Qed.

Open Scope Z_scope.

Definition zlt: forall (x y: Z), {x < y} + {x >= y} := Z_lt_dec.

Lemma zlt_true:
  forall (A: Type) (x y: Z) (a b: A),
  x < y -> (if zlt x y then a else b) = a.
Proof.
  intros. case (zlt x y); intros.
  auto.
  extlia.
Qed.

Lemma zlt_false:
  forall (A: Type) (x y: Z) (a b: A),
  x >= y -> (if zlt x y then a else b) = b.
Proof.
  intros. case (zlt x y); intros.
  extlia.
  auto.
Qed.

Definition zle: forall (x y: Z), {x <= y} + {x > y} := Z_le_gt_dec.

Lemma zle_true:
  forall (A: Type) (x y: Z) (a b: A),
  x <= y -> (if zle x y then a else b) = a.
Proof.
  intros. case (zle x y); intros.
  auto.
  extlia.
Qed.

Lemma zle_false:
  forall (A: Type) (x y: Z) (a b: A),
  x > y -> (if zle x y then a else b) = b.
Proof.
  intros. case (zle x y); intros.
  extlia.
  auto.
Qed.

(** Properties of powers of two. *)

Lemma two_power_nat_O : two_power_nat O = 1.
Proof. reflexivity. Qed.

Lemma two_power_nat_pos : forall n : nat, two_power_nat n > 0.
Proof.
  induction n. rewrite two_power_nat_O. lia.
  rewrite two_power_nat_S. lia.
Qed.

Lemma two_power_nat_two_p:
  forall x, two_power_nat x = two_p (Z.of_nat x).
Proof.
  induction x. auto.
  rewrite two_power_nat_S. rewrite Nat2Z.inj_succ. rewrite two_p_S. lia. lia.
Qed.

Lemma two_p_monotone:
  forall x y, 0 <= x <= y -> two_p x <= two_p y.
Proof.
  intros.
  replace (two_p x) with (two_p x * 1) by lia.
  replace y with (x + (y - x)) by lia.
  rewrite two_p_is_exp; try lia.
  apply Zmult_le_compat_l.
  assert (two_p (y - x) > 0). apply two_p_gt_ZERO. lia. lia.
  assert (two_p x > 0). apply two_p_gt_ZERO. lia. lia.
Qed.

Lemma two_p_monotone_strict:
  forall x y, 0 <= x < y -> two_p x < two_p y.
Proof.
  intros. assert (two_p x <= two_p (y - 1)). apply two_p_monotone; lia.
  assert (two_p (y - 1) > 0). apply two_p_gt_ZERO. lia.
  replace y with (Z.succ (y - 1)) by lia. rewrite two_p_S. lia. lia.
Qed.

Lemma two_p_strict:
  forall x, x >= 0 -> x < two_p x.
Proof.
  intros x0 GT. pattern x0. apply natlike_ind.
  simpl. lia.
  intros. rewrite two_p_S; auto. generalize (two_p_gt_ZERO x H). lia.
  lia.
Qed.

Lemma two_p_strict_2:
  forall x, x >= 0 -> 2 * x - 1 < two_p x.
Proof.
  intros. assert (x = 0 \/ x - 1 >= 0) by lia. destruct H0.
  subst. vm_compute. auto.
  replace (two_p x) with (2 * two_p (x - 1)).
  generalize (two_p_strict _ H0). lia.
  rewrite <- two_p_S. decEq. lia. lia.
Qed.

(** Properties of [Zmin] and [Zmax] *)

Lemma Zmin_spec:
  forall x y, Z.min x y = if zlt x y then x else y.
Proof.
  intros. case (zlt x y); unfold Z.lt, Z.ge; intro z.
  unfold Z.min. rewrite z. auto.
  unfold Z.min. caseEq (x ?= y); intro.
  apply Z.compare_eq. auto.
  contradiction.
  reflexivity.
Qed.

Lemma Zmax_spec:
  forall x y, Z.max x y = if zlt y x then x else y.
Proof.
  intros. case (zlt y x); unfold Z.lt, Z.ge; intro z.
  unfold Z.max. rewrite <- (Zcompare_antisym y x).
  rewrite z. simpl. auto.
  unfold Z.max. rewrite <- (Zcompare_antisym y x).
  caseEq (y ?= x); intro; simpl.
  symmetry. apply Z.compare_eq. auto.
  contradiction. reflexivity.
Qed.

Lemma Zmax_bound_l:
  forall x y z, x <= y -> x <= Z.max y z.
Proof.
  intros. generalize (Z.le_max_l y z). lia.
Qed.
Lemma Zmax_bound_r:
  forall x y z, x <= z -> x <= Z.max y z.
Proof.
  intros. generalize (Z.le_max_r y z). lia.
Qed.

(** Properties of Euclidean division and modulus. *)

Lemma Zmod_unique:
  forall x y a b,
  x = a * y + b -> 0 <= b < y -> x mod y = b.
Proof.
  intros. subst x. rewrite Z.add_comm.
  rewrite Z_mod_plus. apply Z.mod_small. auto. lia.
Qed.

Lemma Zdiv_unique:
  forall x y a b,
  x = a * y + b -> 0 <= b < y -> x / y = a.
Proof.
  intros. subst x. rewrite Z.add_comm.
  rewrite Z_div_plus. rewrite (Zdiv_small b y H0). lia. lia.
Qed.

Lemma Zdiv_Zdiv:
  forall a b c,
  b > 0 -> c > 0 -> (a / b) / c = a / (b * c).
Proof.
  intros. apply Z.div_div; lia.
Qed.

Lemma Zdiv_interval_1:
  forall lo hi a b,
  lo <= 0 -> hi > 0 -> b > 0 ->
  lo * b <= a < hi * b ->
  lo <= a/b < hi.
Proof.
  intros.
  generalize (Z_div_mod_eq a b H1). generalize (Z_mod_lt a b H1). intros.
  set (q := a/b) in *. set (r := a mod b) in *.
  split.
  assert (lo < (q + 1)).
  apply Zmult_lt_reg_r with b. lia.
  apply Z.le_lt_trans with a. lia.
  replace ((q + 1) * b) with (b * q + b) by ring.
  lia.
  lia.
  apply Zmult_lt_reg_r with b. lia.
  replace (q * b) with (b * q) by ring.
  lia.
Qed.

Lemma Zdiv_interval_2:
  forall lo hi a b,
  lo <= a <= hi -> lo <= 0 -> hi >= 0 -> b > 0 ->
  lo <= a/b <= hi.
Proof.
  intros.
  assert (lo <= a / b < hi+1).
  apply Zdiv_interval_1. lia. lia. auto.
  assert (lo * b <= lo * 1) by (apply Z.mul_le_mono_nonpos_l; lia).
  replace (lo * 1) with lo in H3 by ring.
  assert ((hi + 1) * 1 <= (hi + 1) * b) by (apply Z.mul_le_mono_nonneg_l; lia).
  replace ((hi + 1) * 1) with (hi + 1) in H4 by ring.
  lia.
  lia.
Qed.

Lemma Zmod_recombine:
  forall x a b,
  a > 0 -> b > 0 ->
  x mod (a * b) = ((x/b) mod a) * b + (x mod b).
Proof.
  intros. rewrite (Z.mul_comm a b). rewrite Z.rem_mul_r by lia. ring. 
Qed.

(** Properties of divisibility. *)

Lemma Zdivide_interval:
  forall a b c,
  0 < c -> 0 <= a < b -> (c | a) -> (c | b) -> 0 <= a <= b - c.
Proof.
  intros. destruct H1 as [x EQ1]. destruct H2 as [y EQ2]. subst. destruct H0.
  split. lia. exploit Zmult_lt_reg_r; eauto. intros.
  replace (y * c - c) with ((y - 1) * c) by ring.
  apply Zmult_le_compat_r; lia.
Qed.

(** Conversion from [Z] to [nat]. *)

Lemma Z_to_nat_neg:
  forall n, n <= 0 -> Z.to_nat n = O.
Proof.
  destruct n; unfold Z.le; simpl; auto. congruence.
Qed.

Lemma Z_to_nat_max:
  forall z, Z.of_nat (Z.to_nat z) = Z.max z 0.
Proof.
  intros. destruct (zle 0 z).
- rewrite Z2Nat.id by auto. extlia.
- rewrite Z_to_nat_neg by lia. extlia.
Qed.

(** Alignment: [align n amount] returns the smallest multiple of [amount]
  greater than or equal to [n]. *)

Definition align (n: Z) (amount: Z) :=
  ((n + amount - 1) / amount) * amount.

Lemma align_le: forall x y, y > 0 -> x <= align x y.
Proof.
  intros. unfold align.
  generalize (Z_div_mod_eq (x + y - 1) y H). intro.
  replace ((x + y - 1) / y * y)
      with ((x + y - 1) - (x + y - 1) mod y).
  generalize (Z_mod_lt (x + y - 1) y H). lia.
  rewrite Z.mul_comm. lia.
Qed.

Lemma align_divides: forall x y, y > 0 -> (y | align x y).
Proof.
  intros. unfold align. apply Z.divide_factor_r.
Qed.

Lemma align_lt: forall x y, y > 0 -> align x y < x + y.
Proof.
  intros. unfold align.
  generalize (Z_div_mod_eq (x + y - 1) y H); intro.
  generalize (Z_mod_lt (x + y - 1) y H); intro.
  lia.
Qed.

Lemma align_same:
  forall x y, y > 0 -> (y | x) -> align x y = x.
Proof.
  unfold align; intros. destruct H0 as [k E].
  replace (x  + y - 1) with (x + (y - 1)) by lia.
  rewrite E, Z.div_add_l, Z.div_small by lia.
  lia.
Qed.

(** Floor: [floor n amount] returns the greatest multiple of [amount]
    less than or equal to [n]. *)

Definition floor (n: Z) (amount: Z) := (n / amount) * amount.

Lemma floor_interval:
  forall x y, y > 0 -> floor x y <= x < floor x y + y.
Proof.
  unfold floor; intros.
  generalize (Z_div_mod_eq x y H) (Z_mod_lt x y H).
  set (q := x / y). set (r := x mod y). intros. lia.
Qed.

Lemma floor_divides:
  forall x y, y > 0 -> (y | floor x y).
Proof.
  unfold floor; intros. exists (x / y); auto.
Qed.

Lemma floor_same:
  forall x y, y > 0 -> (y | x) -> floor x y = x.
Proof.
  unfold floor; intros. rewrite (Zdivide_Zdiv_eq y x) at 2; auto; lia.
Qed.

Lemma floor_align_interval:
  forall x y, y > 0 ->
  floor x y <= align x y <= floor x y + y.
Proof.
  unfold floor, align; intros.
  replace (x / y * y + y) with ((x + 1 * y) / y * y).
  assert (A: forall a b, a <= b -> a / y * y <= b / y * y).
  { intros. apply Z.mul_le_mono_nonneg_r. lia. apply Z.div_le_mono; lia. }
  split; apply A; lia.
  rewrite Z.div_add by lia. lia.
Qed.

(** * Definitions and theorems on the data types [option], [sum] and [list] *)

Set Implicit Arguments.

(** Comparing option types. *)

Definition option_eq (A: Type) (eqA: forall (x y: A), {x=y} + {x<>y}):
  forall (x y: option A), {x=y} + {x<>y}.
Proof. decide equality. Defined.
Global Opaque option_eq.

(** Lifting a relation to an option type. *)

Inductive option_rel (A B: Type) (R: A -> B -> Prop) : option A -> option B -> Prop :=
  | option_rel_none: option_rel R None None
  | option_rel_some: forall x y, R x y -> option_rel R (Some x) (Some y).

(** Mapping a function over an option type. *)

Definition option_map (A B: Type) (f: A -> B) (x: option A) : option B :=
  match x with
  | None => None
  | Some y => Some (f y)
  end.

(** Mapping a function over a sum type. *)

Definition sum_left_map (A B C: Type) (f: A -> B) (x: A + C) : B + C :=
  match x with
  | inl y => inl C (f y)
  | inr z => inr B z
  end.

(** Properties of [List.nth] (n-th element of a list). *)

Global Hint Resolve in_eq in_cons: coqlib.

Lemma nth_error_in:
  forall (A: Type) (n: nat) (l: list A) (x: A),
  List.nth_error l n = Some x -> In x l.
Proof.
  induction n; simpl.
    destruct l; intros.
    discriminate.
    injection H; intro; subst a. apply in_eq.
    destruct l; intros.
    discriminate.
    apply in_cons. auto.
Qed.
Global Hint Resolve nth_error_in: coqlib.

Lemma nth_error_nil:
  forall (A: Type) (idx: nat), nth_error (@nil A) idx = None.
Proof.
  induction idx; simpl; intros; reflexivity.
Qed.
Global Hint Resolve nth_error_nil: coqlib.

(** Compute the length of a list, with result in [Z]. *)

Fixpoint list_length_z_aux (A: Type) (l: list A) (acc: Z) {struct l}: Z :=
  match l with
  | nil => acc
  | hd :: tl => list_length_z_aux tl (Z.succ acc)
  end.

Remark list_length_z_aux_shift:
  forall (A: Type) (l: list A) n m,
  list_length_z_aux l n = list_length_z_aux l m + (n - m).
Proof.
  induction l; intros; simpl.
  lia.
  replace (n - m) with (Z.succ n - Z.succ m) by lia. auto.
Qed.

Definition list_length_z (A: Type) (l: list A) : Z :=
  list_length_z_aux l 0.

Lemma list_length_z_cons:
  forall (A: Type) (hd: A) (tl: list A),
  list_length_z (hd :: tl) = list_length_z tl + 1.
Proof.
  intros. unfold list_length_z. simpl.
  rewrite (list_length_z_aux_shift tl 1 0). lia.
Qed.

Lemma list_length_z_pos:
  forall (A: Type) (l: list A),
  list_length_z l >= 0.
Proof.
  induction l; simpl. unfold list_length_z; simpl. lia.
  rewrite list_length_z_cons. lia.
Qed.

Lemma list_length_z_map:
  forall (A B: Type) (f: A -> B) (l: list A),
  list_length_z (map f l) = list_length_z l.
Proof.
  induction l. reflexivity. simpl. repeat rewrite list_length_z_cons. congruence.
Qed.

(** Extract the n-th element of a list, as [List.nth_error] does,
    but the index [n] is of type [Z]. *)

Fixpoint list_nth_z (A: Type) (l: list A) (n: Z) {struct l}: option A :=
  match l with
  | nil => None
  | hd :: tl => if zeq n 0 then Some hd else list_nth_z tl (Z.pred n)
  end.

Lemma list_nth_z_in:
  forall (A: Type) (l: list A) n x,
  list_nth_z l n = Some x -> In x l.
Proof.
  induction l; simpl; intros.
  congruence.
  destruct (zeq n 0). left; congruence. right; eauto.
Qed.

Lemma list_nth_z_map:
  forall (A B: Type) (f: A -> B) (l: list A) n,
  list_nth_z (List.map f l) n = option_map f (list_nth_z l n).
Proof.
  induction l; simpl; intros.
  auto.
  destruct (zeq n 0). auto. eauto.
Qed.

Lemma list_nth_z_range:
  forall (A: Type) (l: list A) n x,
  list_nth_z l n = Some x -> 0 <= n < list_length_z l.
Proof.
  induction l; simpl; intros.
  discriminate.
  rewrite list_length_z_cons. destruct (zeq n 0).
  generalize (list_length_z_pos l); lia.
  exploit IHl; eauto. lia.
Qed.

(** Properties of [List.incl] (list inclusion). *)

Lemma incl_cons_inv:
  forall (A: Type) (a: A) (b c: list A),
  incl (a :: b) c -> incl b c.
Proof.
  unfold incl; intros. apply H. apply in_cons. auto.
Qed.
Global Hint Resolve incl_cons_inv: coqlib.

Lemma incl_app_inv_l:
  forall (A: Type) (l1 l2 m: list A),
  incl (l1 ++ l2) m -> incl l1 m.
Proof.
  unfold incl; intros. apply H. apply in_or_app. left; assumption.
Qed.

Lemma incl_app_inv_r:
  forall (A: Type) (l1 l2 m: list A),
  incl (l1 ++ l2) m -> incl l2 m.
Proof.
  unfold incl; intros. apply H. apply in_or_app. right; assumption.
Qed.

Global Hint Resolve  incl_tl incl_refl incl_app_inv_l incl_app_inv_r: coqlib.

Lemma incl_same_head:
  forall (A: Type) (x: A) (l1 l2: list A),
  incl l1 l2 -> incl (x::l1) (x::l2).
Proof.
  intros; red; simpl; intros. intuition.
Qed.

(** Properties of [List.map] (mapping a function over a list). *)

Lemma list_map_exten:
  forall (A B: Type) (f f': A -> B) (l: list A),
  (forall x, In x l -> f x = f' x) ->
  List.map f' l = List.map f l.
Proof.
  induction l; simpl; intros.
  reflexivity.
  rewrite <- H. rewrite IHl. reflexivity.
  intros. apply H. tauto.
  tauto.
Qed.

Lemma list_map_compose:
  forall (A B C: Type) (f: A -> B) (g: B -> C) (l: list A),
  List.map g (List.map f l) = List.map (fun x => g(f x)) l.
Proof.
  induction l; simpl. reflexivity. rewrite IHl; reflexivity.
Qed.

Lemma list_map_identity:
  forall (A: Type) (l: list A),
  List.map (fun (x:A) => x) l = l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma list_map_nth:
  forall (A B: Type) (f: A -> B) (l: list A) (n: nat),
  nth_error (List.map f l) n = option_map f (nth_error l n).
Proof.
  induction l; simpl; intros.
  repeat rewrite nth_error_nil. reflexivity.
  destruct n; simpl. reflexivity. auto.
Qed.

Lemma list_length_map:
  forall (A B: Type) (f: A -> B) (l: list A),
  List.length (List.map f l) = List.length l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma list_in_map_inv:
  forall (A B: Type) (f: A -> B) (l: list A) (y: B),
  In y (List.map f l) -> exists x:A, y = f x /\ In x l.
Proof.
  induction l; simpl; intros.
  contradiction.
  elim H; intro.
  exists a; intuition auto.
  generalize (IHl y H0). intros [x [EQ IN]].
  exists x; tauto.
Qed.

Lemma list_append_map:
  forall (A B: Type) (f: A -> B) (l1 l2: list A),
  List.map f (l1 ++ l2) = List.map f l1 ++ List.map f l2.
Proof.
  induction l1; simpl; intros.
  auto. rewrite IHl1. auto.
Qed.

Lemma list_append_map_inv:
  forall (A B: Type) (f: A -> B) (m1 m2: list B) (l: list A),
  List.map f l = m1 ++ m2 ->
  exists l1, exists l2, List.map f l1 = m1 /\ List.map f l2 = m2 /\ l = l1 ++ l2.
Proof.
  induction m1; simpl; intros.
  exists (@nil A); exists l; auto.
  destruct l; simpl in H; inv H.
  exploit IHm1; eauto. intros [l1 [l2 [P [Q R]]]]. subst l.
  exists (a0 :: l1); exists l2; intuition. simpl; congruence.
Qed.

(** Properties of [List.app] (concatenation) *)

Lemma list_append_injective_l:
  forall (A: Type) (l1 l2 l1' l2': list A),
  l1 ++ l2 = l1' ++ l2' -> List.length l1 = List.length l1' -> l1 = l1' /\ l2 = l2'.
Proof.
  intros until l2'. revert l1 l1'. induction l1 as [ | a l1]; destruct l1' as [ | a' l1']; simpl; intros.
- auto.
- discriminate.
- discriminate.
- destruct (IHl1 l1'). congruence. congruence. split; congruence.
Qed.

Lemma list_append_injective_r:
  forall (A: Type) (l1 l2 l1' l2': list A),
  l1 ++ l2 = l1' ++ l2' -> List.length l2 = List.length l2' -> l1 = l1' /\ l2 = l2'.
Proof.
  intros.
  assert (X: rev l2 = rev l2' /\ rev l1 = rev l1').
  { apply list_append_injective_l.
    rewrite <- ! rev_app_distr. congruence.
    rewrite ! rev_length; auto. }
  rewrite <- (rev_involutive l1), <- (rev_involutive l1'), <- (rev_involutive l2), <- (rev_involutive l2').
  intuition congruence.
Qed.

(** Folding a function over a list *)

Section LIST_FOLD.

Variables A B: Type.
Variable f: A -> B -> B.

(** This is exactly [List.fold_left] from Coq's standard library,
  with [f] taking arguments in a different order. *)

Fixpoint list_fold_left (accu: B) (l: list A) : B :=
  match l with nil => accu | x :: l' => list_fold_left (f x accu) l' end.

(** This is exactly [List.fold_right] from Coq's standard library,
  except that it runs in constant stack space. *)

Definition list_fold_right (l: list A) (base: B) : B :=
  list_fold_left base (List.rev' l).

Remark list_fold_left_app:
  forall l1 l2 accu,
  list_fold_left accu (l1 ++ l2) = list_fold_left (list_fold_left accu l1) l2.
Proof.
  induction l1; simpl; intros.
  auto.
  rewrite IHl1. auto.
Qed.

Lemma list_fold_right_eq:
  forall l base,
  list_fold_right l base =
  match l with nil => base | x :: l' => f x (list_fold_right l' base) end.
Proof.
  unfold list_fold_right; intros.
  destruct l.
  auto.
  unfold rev'. rewrite <- ! rev_alt. simpl.
  rewrite list_fold_left_app. simpl. auto.
Qed.

Lemma list_fold_right_spec:
  forall l base, list_fold_right l base = List.fold_right f base l.
Proof.
  induction l; simpl; intros; rewrite list_fold_right_eq; congruence.
Qed.

End LIST_FOLD.

(** Properties of list membership. *)

Lemma in_cns:
  forall (A: Type) (x y: A) (l: list A), In x (y :: l) <-> y = x \/ In x l.
Proof.
  intros. simpl. tauto.
Qed.

Lemma in_app:
  forall (A: Type) (x: A) (l1 l2: list A), In x (l1 ++ l2) <-> In x l1 \/ In x l2.
Proof.
  intros. split; intro. apply in_app_or. auto. apply in_or_app. auto.
Qed.

Lemma list_in_insert:
  forall (A: Type) (x: A) (l1 l2: list A) (y: A),
  In x (l1 ++ l2) -> In x (l1 ++ y :: l2).
Proof.
  intros. apply in_or_app; simpl. elim (in_app_or _ _ _ H); intro; auto.
Qed.

(** [list_disjoint l1 l2] holds iff [l1] and [l2] have no elements
  in common. *)

Definition list_disjoint (A: Type) (l1 l2: list A) : Prop :=
  forall (x y: A), In x l1 -> In y l2 -> x <> y.

Lemma list_disjoint_cons_l:
  forall (A: Type) (a: A) (l1 l2: list A),
  list_disjoint l1 l2 -> ~In a l2 -> list_disjoint (a :: l1) l2.
Proof.
  unfold list_disjoint; simpl; intros. destruct H1. congruence. apply H; auto.
Qed.

Lemma list_disjoint_cons_r:
  forall (A: Type) (a: A) (l1 l2: list A),
  list_disjoint l1 l2 -> ~In a l1 -> list_disjoint l1 (a :: l2).
Proof.
  unfold list_disjoint; simpl; intros. destruct H2. congruence. apply H; auto.
Qed.

Lemma list_disjoint_cons_left:
  forall (A: Type) (a: A) (l1 l2: list A),
  list_disjoint (a :: l1) l2 -> list_disjoint l1 l2.
Proof.
  unfold list_disjoint; simpl; intros. apply H; tauto.
Qed.

Lemma list_disjoint_cons_right:
  forall (A: Type) (a: A) (l1 l2: list A),
  list_disjoint l1 (a :: l2) -> list_disjoint l1 l2.
Proof.
  unfold list_disjoint; simpl; intros. apply H; tauto.
Qed.

Lemma list_disjoint_notin:
  forall (A: Type) (l1 l2: list A) (a: A),
  list_disjoint l1 l2 -> In a l1 -> ~(In a l2).
Proof.
  unfold list_disjoint; intros; red; intros.
  apply H with a a; auto.
Qed.

Lemma list_disjoint_sym:
  forall (A: Type) (l1 l2: list A),
  list_disjoint l1 l2 -> list_disjoint l2 l1.
Proof.
  unfold list_disjoint; intros.
  apply not_eq_sym. apply H; auto.
Qed.

Lemma list_disjoint_dec:
  forall (A: Type) (eqA_dec: forall (x y: A), {x=y} + {x<>y}) (l1 l2: list A),
  {list_disjoint l1 l2} + {~list_disjoint l1 l2}.
Proof.
  induction l1; intros.
  left; red; intros. elim H.
  case (In_dec eqA_dec a l2); intro.
  right; red; intro. apply (H a a); auto with coqlib.
  case (IHl1 l2); intro.
  left; red; intros. elim H; intro.
    red; intro; subst a y. contradiction.
    apply l; auto.
  right; red; intros. elim n0. eapply list_disjoint_cons_left; eauto.
Defined.

(** [list_equiv l1 l2] holds iff the lists [l1] and [l2] contain the same elements. *)

Definition list_equiv (A : Type) (l1 l2: list A) : Prop :=
  forall x, In x l1 <-> In x l2.

(** [list_norepet l] holds iff the list [l] contains no repetitions,
  i.e. no element occurs twice. *)

Inductive list_norepet (A: Type) : list A -> Prop :=
  | list_norepet_nil:
      list_norepet nil
  | list_norepet_cons:
      forall hd tl,
      ~(In hd tl) -> list_norepet tl -> list_norepet (hd :: tl).

Lemma list_norepet_dec:
  forall (A: Type) (eqA_dec: forall (x y: A), {x=y} + {x<>y}) (l: list A),
  {list_norepet l} + {~list_norepet l}.
Proof.
  induction l.
  left; constructor.
  destruct IHl.
  case (In_dec eqA_dec a l); intro.
  right. red; intro. inversion H. contradiction.
  left. constructor; auto.
  right. red; intro. inversion H. contradiction.
Defined.

Lemma list_map_norepet:
  forall (A B: Type) (f: A -> B) (l: list A),
  list_norepet l ->
  (forall x y, In x l -> In y l -> x <> y -> f x <> f y) ->
  list_norepet (List.map f l).
Proof.
  induction 1; simpl; intros.
  constructor.
  constructor.
  red; intro. generalize (list_in_map_inv f _ _ H2).
  intros [x [EQ IN]]. generalize EQ. change (f hd <> f x).
  apply H1. tauto. tauto.
  red; intro; subst x. contradiction.
  apply IHlist_norepet. intros. apply H1. tauto. tauto. auto.
Qed.

Remark list_norepet_append_commut:
  forall (A: Type) (a b: list A),
  list_norepet (a ++ b) -> list_norepet (b ++ a).
Proof.
  intro A.
  assert (forall (x: A) (b: list A) (a: list A),
            list_norepet (a ++ b) -> ~(In x a) -> ~(In x b) ->
            list_norepet (a ++ x :: b)).
    induction a; simpl; intros.
    constructor; auto.
    inversion H. constructor. red; intro.
    elim (in_app_or _ _ _ H6); intro.
    elim H4. apply in_or_app. tauto.
    elim H7; intro. subst a. elim H0. left. auto.
    elim H4. apply in_or_app. tauto.
    auto.
  induction a; simpl; intros.
  rewrite <- app_nil_end. auto.
  inversion H0. apply H. auto.
  red; intro; elim H3. apply in_or_app. tauto.
  red; intro; elim H3. apply in_or_app. tauto.
Qed.

Lemma list_norepet_app:
  forall (A: Type) (l1 l2: list A),
  list_norepet (l1 ++ l2) <->
  list_norepet l1 /\ list_norepet l2 /\ list_disjoint l1 l2.
Proof.
  induction l1; simpl; intros; split; intros.
  intuition. constructor. red;simpl;auto.
  tauto.
  inversion H; subst. rewrite IHl1 in H3. rewrite in_app in H2.
  intuition.
  constructor; auto. red; intros. elim H2; intro. congruence. auto.
  destruct H as [B [C D]]. inversion B; subst.
  constructor. rewrite in_app. intuition. elim (D a a); auto. apply in_eq.
  rewrite IHl1. intuition. red; intros. apply D; auto. apply in_cons; auto.
Qed.

Lemma list_norepet_append:
  forall (A: Type) (l1 l2: list A),
  list_norepet l1 -> list_norepet l2 -> list_disjoint l1 l2 ->
  list_norepet (l1 ++ l2).
Proof.
  generalize list_norepet_app; firstorder.
Qed.

Lemma list_norepet_append_right:
  forall (A: Type) (l1 l2: list A),
  list_norepet (l1 ++ l2) -> list_norepet l2.
Proof.
  generalize list_norepet_app; firstorder.
Qed.

Lemma list_norepet_append_left:
  forall (A: Type) (l1 l2: list A),
  list_norepet (l1 ++ l2) -> list_norepet l1.
Proof.
  generalize list_norepet_app; firstorder.
Qed.

Lemma list_norepet_rev:
  forall (A: Type) (l: list A), list_norepet l -> list_norepet (List.rev l).
Proof.
  induction 1; simpl.
- constructor.
- apply list_norepet_append_commut. simpl. constructor; auto. rewrite <- List.in_rev; auto.
Qed.

(** [is_tail l1 l2] holds iff [l2] is of the form [l ++ l1] for some [l]. *)

Inductive is_tail (A: Type): list A -> list A -> Prop :=
  | is_tail_refl:
      forall c, is_tail c c
  | is_tail_cons:
      forall i c1 c2, is_tail c1 c2 -> is_tail c1 (i :: c2).

Lemma is_tail_in:
  forall (A: Type) (i: A) c1 c2, is_tail (i :: c1) c2 -> In i c2.
Proof.
  induction c2; simpl; intros.
  inversion H.
  inversion H. tauto. right; auto.
Qed.

Lemma is_tail_cons_left:
  forall (A: Type) (i: A) c1 c2, is_tail (i :: c1) c2 -> is_tail c1 c2.
Proof.
  induction c2; intros; inversion H.
  constructor. constructor. constructor. auto.
Qed.

Global Hint Resolve is_tail_refl is_tail_cons is_tail_in is_tail_cons_left: coqlib.

Lemma is_tail_incl:
  forall (A: Type) (l1 l2: list A), is_tail l1 l2 -> incl l1 l2.
Proof.
  induction 1; eauto with coqlib.
Qed.

Lemma is_tail_trans:
  forall (A: Type) (l1 l2: list A),
  is_tail l1 l2 -> forall (l3: list A), is_tail l2 l3 -> is_tail l1 l3.
Proof.
  induction 1; intros. auto. apply IHis_tail. eapply is_tail_cons_left; eauto.
Qed.

(** [list_forall2 P [x1 ... xN] [y1 ... yM]] holds iff [N = M] and
  [P xi yi] holds for all [i]. *)

Section FORALL2.

Variable A: Type.
Variable B: Type.
Variable P: A -> B -> Prop.

Inductive list_forall2: list A -> list B -> Prop :=
  | list_forall2_nil:
      list_forall2 nil nil
  | list_forall2_cons:
      forall a1 al b1 bl,
      P a1 b1 ->
      list_forall2 al bl ->
      list_forall2 (a1 :: al) (b1 :: bl).

Lemma list_forall2_app:
  forall a2 b2 a1 b1,
  list_forall2 a1 b1 -> list_forall2 a2 b2 ->
  list_forall2 (a1 ++ a2) (b1 ++ b2).
Proof.
  induction 1; intros; simpl. auto. constructor; auto.
Qed.

Lemma list_forall2_length:
  forall l1 l2,
  list_forall2 l1 l2 -> length l1 = length l2.
Proof.
  induction 1; simpl; congruence.
Qed.

Lemma list_forall2_in_left:
  forall x1 l1 l2,
  list_forall2 l1 l2 -> In x1 l1 -> exists x2, In x2 l2 /\ P x1 x2.
Proof.
  induction 1; simpl; intros. contradiction. destruct H1.
  subst; exists b1; auto.
  exploit IHlist_forall2; eauto. intros (x2 & U & V); exists x2; auto.
Qed.

Lemma list_forall2_in_right:
  forall x2 l1 l2,
  list_forall2 l1 l2 -> In x2 l2 -> exists x1, In x1 l1 /\ P x1 x2.
Proof.
  induction 1; simpl; intros. contradiction. destruct H1.
  subst; exists a1; auto.
  exploit IHlist_forall2; eauto. intros (x1 & U & V); exists x1; auto.
Qed.

End FORALL2.

Lemma list_forall2_imply:
  forall (A B: Type) (P1: A -> B -> Prop) (l1: list A) (l2: list B),
  list_forall2 P1 l1 l2 ->
  forall (P2: A -> B -> Prop),
  (forall v1 v2, In v1 l1 -> In v2 l2 -> P1 v1 v2 -> P2 v1 v2) ->
  list_forall2 P2 l1 l2.
Proof.
  induction 1; intros.
  constructor.
  constructor. auto with coqlib. apply IHlist_forall2; auto.
  intros. auto with coqlib.
Qed.

(** Dropping the first N elements of a list. *)

Fixpoint list_drop (A: Type) (n: nat) (x: list A) {struct n} : list A :=
  match n with
  | O => x
  | S n' => match x with nil => nil | hd :: tl => list_drop n' tl end
  end.

Lemma list_drop_incl:
  forall (A: Type) (x: A) n (l: list A), In x (list_drop n l) -> In x l.
Proof.
  induction n; simpl; intros. auto.
  destruct l; auto with coqlib.
Qed.

Lemma list_drop_norepet:
  forall (A: Type) n (l: list A), list_norepet l -> list_norepet (list_drop n l).
Proof.
  induction n; simpl; intros. auto.
  inv H. constructor. auto.
Qed.

Lemma list_map_drop:
  forall (A B: Type) (f: A -> B) n (l: list A),
  list_drop n (map f l) = map f (list_drop n l).
Proof.
  induction n; simpl; intros. auto.
  destruct l; simpl; auto.
Qed.

(** * Definitions and theorems over boolean types *)

Definition proj_sumbool {P Q: Prop} (a: {P} + {Q}) : bool :=
  if a then true else false.

Coercion proj_sumbool: sumbool >-> bool.

Lemma proj_sumbool_true:
  forall (P Q: Prop) (a: {P}+{Q}), proj_sumbool a = true -> P.
Proof.
  intros P Q a. destruct a; simpl. auto. congruence.
Qed.

Lemma proj_sumbool_is_true:
  forall (P: Prop) (a: {P}+{~P}), P -> proj_sumbool a = true.
Proof.
  intros. unfold proj_sumbool. destruct a. auto. contradiction.
Qed.

Ltac InvBooleans :=
  match goal with
  | [ H: _ && _ = true |- _ ] =>
      destruct (andb_prop _ _ H); clear H; InvBooleans
  | [ H: _ || _ = false |- _ ] =>
      destruct (orb_false_elim _ _ H); clear H; InvBooleans
  | [ H: proj_sumbool ?x = true |- _ ] =>
      generalize (proj_sumbool_true _ H); clear H; intro; InvBooleans
  | _ => idtac
  end.

Section DECIDABLE_EQUALITY.

Variable A: Type.
Variable dec_eq: forall (x y: A), {x=y} + {x<>y}.
Variable B: Type.

Lemma dec_eq_true:
  forall (x: A) (ifso ifnot: B),
  (if dec_eq x x then ifso else ifnot) = ifso.
Proof.
  intros. destruct (dec_eq x x). auto. congruence.
Qed.

Lemma dec_eq_false:
  forall (x y: A) (ifso ifnot: B),
  x <> y -> (if dec_eq x y then ifso else ifnot) = ifnot.
Proof.
  intros. destruct (dec_eq x y). congruence. auto.
Qed.

Lemma dec_eq_sym:
  forall (x y: A) (ifso ifnot: B),
  (if dec_eq x y then ifso else ifnot) =
  (if dec_eq y x then ifso else ifnot).
Proof.
  intros. destruct (dec_eq x y).
  subst y. rewrite dec_eq_true. auto.
  rewrite dec_eq_false; auto.
Qed.

End DECIDABLE_EQUALITY.

Section DECIDABLE_PREDICATE.

Variable P: Prop.
Variable dec: {P} + {~P}.
Variable A: Type.

Lemma pred_dec_true:
  forall (a b: A), P -> (if dec then a else b) = a.
Proof.
  intros. destruct dec. auto. contradiction.
Qed.

Lemma pred_dec_false:
  forall (a b: A), ~P -> (if dec then a else b) = b.
Proof.
  intros. destruct dec. contradiction. auto.
Qed.

End DECIDABLE_PREDICATE.

(** * Well-founded orderings *)

Require Import Relations.

(** A non-dependent version of lexicographic ordering. *)

Section LEX_ORDER.

Variable A: Type.
Variable B: Type.
Variable ordA: A -> A -> Prop.
Variable ordB: B -> B -> Prop.

Inductive lex_ord: A*B -> A*B -> Prop :=
  | lex_ord_left: forall a1 b1 a2 b2,
      ordA a1 a2 -> lex_ord (a1,b1) (a2,b2)
  | lex_ord_right: forall a b1 b2,
      ordB b1 b2 -> lex_ord (a,b1) (a,b2).

Lemma wf_lex_ord:
  well_founded ordA -> well_founded ordB -> well_founded lex_ord.
Proof.
  intros Awf Bwf.
  assert (forall a, Acc ordA a -> forall b, Acc ordB b -> Acc lex_ord (a, b)).
    induction 1. induction 1. constructor; intros. inv H3.
    apply H0. auto. apply Bwf.
    apply H2; auto.
  red; intros. destruct a as [a b]. apply H; auto.
Qed.

Lemma transitive_lex_ord:
  transitive _ ordA -> transitive _ ordB -> transitive _ lex_ord.
Proof.
  intros trA trB; red; intros.
  inv H; inv H0.
  left; eapply trA; eauto.
  left; auto.
  left; auto.
  right; eapply trB; eauto.
Qed.

End LEX_ORDER.

(** * Nonempty lists *)

Inductive nlist (A: Type) : Type :=
  | nbase: A -> nlist A
  | ncons: A -> nlist A -> nlist A.

Definition nfirst {A: Type} (l: nlist A) :=
  match l with nbase a => a | ncons a l' => a end.

Fixpoint nlast {A: Type} (l: nlist A) :=
  match l with nbase a => a | ncons a l' => nlast l' end.

Fixpoint nIn {A: Type} (x: A) (l: nlist A) : Prop :=
  match l with
  | nbase a => a = x
  | ncons a l => a = x \/ nIn x l
  end.

Inductive nlist_forall2 {A B: Type} (R: A -> B -> Prop) : nlist A -> nlist B -> Prop :=
  | nbase_forall2: forall a b, R a b -> nlist_forall2 R (nbase a) (nbase b)
  | ncons_forall2: forall a l b m, R a b -> nlist_forall2 R l m -> nlist_forall2 R (ncons a l) (ncons b m).

Lemma nlist_forall2_imply:
  forall (A B: Type) (P1: A -> B -> Prop) (l1: nlist A) (l2: nlist B),
  nlist_forall2 P1 l1 l2 ->
  forall (P2: A -> B -> Prop),
  (forall v1 v2, nIn v1 l1 -> nIn v2 l2 -> P1 v1 v2 -> P2 v1 v2) ->
  nlist_forall2 P2 l1 l2.
Proof.
  induction 1; simpl; intros; constructor; auto.
Qed.
    
 (* begin IntvSets.v
 *)

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
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

(** Finite sets of integer intervals *)

(** "Raw", non-dependent implementation.  A set of intervals is a
  list of nonempty semi-open intervals [(lo, hi)],
  sorted in increasing order of the low bound,
  and with no overlap nor adjacency between elements.
  In particular, if the list contains [(lo1, hi1)] followed by [(lo2, hi2)],
  we have [lo1 < hi1 < lo2 < hi2]. *)

Require Import MirrorSolve.FirstOrder.

Section IntvSets.

  (*** MS BEGIN {"type": "definition"} *)
  Inductive t : Type := Nil | Cons (lo hi: Z) (tl: t).

  Fixpoint In (x: Z) (s: t) :=
    match s with
    | Nil => False
    | Cons l h s' => l <= x < h \/ In x s'
    end.

  Inductive ok: t -> Prop :=
    | ok_nil: ok Nil
    | ok_cons: forall l h s
        (BOUNDS: l < h)
        (BELOW: forall x, In x s -> h < x)
        (OK: ok s),
        ok (Cons l h s).
  Fixpoint ok' (x: t) : Prop := 
    match x with 
    | Nil => True
    | (Cons l h s) => 
      l < h /\ (forall x, In x s -> h < x) /\ ok' s
    end.
  Lemma ok_ok' : forall x, ok x <-> ok' x.
    induction x; 
    simpl in *;
    intuition;
    simpl in *;
    intuition (econstructor || eauto).
    - inversion H1; subst;
      eauto.
    - inversion H1; subst; eauto.
    - eapply H;
      inversion H1;
      eauto.
    - eauto.
    - eapply H1.
    - eauto.
  Qed.

  Fixpoint mem (x: Z) (s: t) : bool :=
    match s with
    | Nil => false
    | Cons l h s' => ite (A := bool) (Z.ltb x h) (Z.leb l x) (mem x s')
    end.

  Fixpoint contains (L H: Z) (s: t) : bool :=
    match s with
    | Nil => false
    | Cons l h s' => (Z.leb H h && Z.leb l L) || contains L H s'
    end.

  Fixpoint add (L H: Z) (s: t) {struct s} : t :=
    match s with
    | Nil => Cons L H Nil
    | Cons l h s' =>
        ite (Z.ltb h L) (Cons l h (add L H s'))
        (ite (Z.ltb H l) (Cons L H s)
        (add (Z.min l L) (Z.max h H) s'))
    end.
  
  Fixpoint remove (L H: Z) (s: t) {struct s} : t :=
    match s with
    | Nil => Nil
    | Cons l h s' =>
        ite (Z.ltb h L) (Cons l h (remove L H s'))
        (ite (Z.ltb H l) s
        (ite (Z.ltb l L)
          (ite (Z.ltb H h) (Cons l L (Cons H h s')) (Cons l L (remove L H s')))
          (ite (Z.ltb H h) (Cons H h s') (remove L H s'))))
    end.

  Fixpoint inter (s1 s2: t) {struct s1} : t :=
    let fix intr (s2: t) : t :=
      match s1, s2 with
      | Nil, _ => Nil
      | _, Nil => Nil
      | Cons l1 h1 s1', Cons l2 h2 s2' =>
          if zle h1 l2 then inter s1' s2
          else if zle h2 l1 then intr s2'
          else if zle l1 l2 then
            if zle h2 h1 then Cons l2 h2 (intr s2') else Cons l2 h1 (inter s1' s2)
          else
            if zle h1 h2 then Cons l1 h1 (inter s1' s2) else Cons l1 h2 (intr s2')
      end
    in intr s2.
  
  Fixpoint union (s1 s2: t) : t :=
    match s1, s2 with
    | Nil, _ => s2
    | _, Nil => s1
    | Cons l1 h1 s1', Cons l2 h2 s2' => add l1 h1 (add l2 h2 (union s1' s2'))
    end.

  Fixpoint beq (s1 s2: t) : bool :=
    match s1, s2 with
    | Nil, Nil => true
    | Cons l1 h1 t1, Cons l2 h2 t2 => Z.eqb l1 l2 && Z.eqb h1 h2 && beq t1 t2
    | _, _ => false
    end.
  (*** MS END {"type": "definition"} *)

  (*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
  Lemma in_nil: 
    forall z, 
      In z Nil <-> False.
  Proof. intros; simpl; intuition. Qed.

  Lemma in_cons: 
    forall x l h t, 
      (l <= x < h \/ In x t) <->
      In x (Cons l h t).
  Proof. intros; simpl; intuition. Qed.

  Lemma ok'_nil: 
    ok' Nil. 
  Proof. intros; simpl; intuition. Qed.

  Lemma ok'_cons: 
    forall l h t, 
      (l < h /\ (forall x, In x t -> h < x) /\ ok' t) <->
      ok' (Cons l h t).
  Proof. intros; simpl; intuition. Qed.
  
  Lemma mem_nil: 
    forall x, 
      mem x Nil = false. 
  Proof. intros; exact eq_refl. Qed.

  Lemma mem_cons: 
    forall x l h t, 
      mem x (Cons l h t) = ite (A := bool) (Z.ltb x h) (Z.leb l x) (mem x t).
  Proof. intros; exact eq_refl. Qed.

  Lemma contains_nil: 
    forall x y, 
      contains x y Nil = false. 
  Proof. intros; exact eq_refl. Qed.

  Lemma contains_cons: 
    forall L H l h t, 
      contains L H (Cons l h t) = (Z.leb H h && Z.leb l L) || contains L H t.
  Proof. intros; exact eq_refl. Qed.

  Lemma add_nil: 
    forall L H, 
      add L H Nil = Cons L H Nil. 
  Proof. intros; exact eq_refl. Qed.

  Lemma add_cons: 
    forall L H l h s', 
      add L H (Cons l h s') = 
      ite (Z.ltb h L) (Cons l h (add L H s'))
        (ite (Z.ltb H l) (Cons L H (Cons l h s'))
        (add (Z.min l L) (Z.max h H) s')).
  Proof. intros; exact eq_refl. Qed.

  Lemma remove_nil: 
    forall L H, 
      remove L H Nil = Nil. 
  Proof. intros; exact eq_refl. Qed.

  Lemma remove_cons: 
    forall L H l h s', 
      remove L H (Cons l h s') = 
      ite (Z.ltb h L) (Cons l h (remove L H s'))
        (ite (Z.ltb H l) (Cons l h s')
        (ite (Z.ltb l L)
          (ite (Z.ltb H h) (Cons l L (Cons H h s')) (Cons l L (remove L H s')))
          (ite (Z.ltb H h) (Cons H h s') (remove L H s')))).
  Proof. intros; exact eq_refl. Qed.

  Lemma union_nil_l: 
    forall s2, 
      union Nil s2 = s2. 
  Proof. intros; exact eq_refl. Qed.
  
  Lemma union_nil_r: 
    forall s1, 
      union s1 Nil = s1. 
  Proof. induction s1; intros; exact eq_refl. Qed.

  Lemma union_cons_cons: 
    forall l1 l2 h1 h2 s1' s2', 
      union (Cons l1 h1 s1') (Cons l2 h2 s2') = 
        add l1 h1 (add l2 h2 (union s1' s2')).
  Proof. intros; exact eq_refl. Qed.

  Lemma beq_nil_nil: 
    beq Nil Nil = true. 
  Proof. intros; exact eq_refl. Qed.

  Lemma beq_nil_cons:
    forall L H s,
      beq Nil (Cons L H s) = false. 
  Proof. intros; exact eq_refl. Qed.
  
  Lemma beq_cons_nil:
    forall L H s,
      beq (Cons L H s) Nil = false. 
  Proof. intros; exact eq_refl. Qed.

  Lemma beq_cons_cons:
    forall l1 h1 t1 l2 h2 t2,
      beq (Cons l1 h1 t1) (Cons l2 h2 t2) = Z.eqb l1 l2 && Z.eqb h1 h2 && beq t1 t2. 
  Proof. intros; exact eq_refl. Qed.
  (*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

  From Equations Require Import Equations.
  Require Import Coq.Program.Equality.
  Require Import Coq.Lists.List.
  
  Require Import MirrorSolve.FirstOrder.
  Require Import MirrorSolve.HLists.
  
  Import ListNotations.
  Import HListNotations.
  
  Require Import Coq.ZArith.BinInt.

  Require Import MirrorSolve.BV.
  Require Import MirrorSolve.SMT.
  Require Import MirrorSolve.UF.

  Require Import MirrorSolve.Reflection.Core.
  Require Import MirrorSolve.Reflection.FM.
  Require Import MirrorSolve.Reflection.Tactics.
  From Hammer Require Import Hammer.

  Set Hammer ATPLimit 5.
  Set Hammer ReconstrLimit 10.
  
  (*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
  Inductive sorts : Set := | BS | ZS | TS.
  
  Scheme Equality for sorts.
  Set Universe Polymorphism.
  
  Inductive funs: arity sorts -> sorts -> Type :=
    | b_lit : forall (b: bool), funs [] BS
    | z_lt : funs [ZS; ZS] BS
    | z_le : funs [ZS; ZS] BS
    | z_gt : funs [ZS; ZS] BS
    | z_ge : funs [ZS; ZS] BS
    | z_eqb : funs [ZS; ZS] BS
    | z_max : funs [ZS; ZS] ZS
    | z_min : funs [ZS; ZS] ZS
    | nil_f : funs [] TS
    | cons_f : funs [ZS; ZS; TS] TS
    | mem_f : funs [ZS; TS] BS
    | contains_f : funs [ZS; ZS; TS] BS
    | add_f : funs [ZS; ZS; TS] TS
    | remove_f : funs [ZS; ZS; TS] TS
    | union_f : funs [TS; TS] TS
    | beq_f : funs [TS; TS] BS
    | cond_b : funs [BS; BS; BS] BS
    | cond_t : funs [BS; TS; TS] TS
    | cond_z : funs [BS; ZS; ZS] ZS
    | b_and : funs [BS; BS] BS
    | b_or : funs [BS; BS] BS. 
  
  Inductive rels: arity sorts -> Type :=
    | lt_z : rels [ZS; ZS] 
    | gt_z : rels [ZS; ZS]
    | le_z : rels [ZS; ZS]
    | in_r : rels [ZS; TS]
    | ok_r : rels [TS].
  
  Definition sig: signature :=
    {| sig_sorts := sorts;
      sig_funs := funs;
      sig_rels := rels |}.

  Definition fm ctx := FirstOrder.fm sig ctx.
  Definition tm ctx := FirstOrder.tm sig ctx.

  Definition mod_sorts (s: sig_sorts sig) : Type :=
    match s with
    | TS => t
    | ZS => Z
    | BS => bool
    end.
  
  Local Obligation Tactic := idtac.
  Equations 
    mod_fns {params ret} (f: sig_funs sig params ret) (args: HList.t mod_sorts params) 
    : mod_sorts ret :=
    { 
      mod_fns (b_lit b) _ := b;
      mod_fns z_lt (l ::: r ::: _) := (l <? r)%Z;
      mod_fns z_le (l ::: r ::: _) := (Z.leb l r)%Z;
      mod_fns z_gt (l ::: r ::: _) := (l >? r)%Z;
      mod_fns z_ge (l ::: r ::: _) := (Z.geb l r)%Z;
      mod_fns z_eqb (l ::: r ::: _) := (Z.eqb l r)%Z;
      mod_fns z_max (l ::: r ::: _) := Z.max l r;
      mod_fns z_min (l ::: r ::: _) := Z.min l r;
      mod_fns nil_f _ := IntvSets.Nil;
      mod_fns cons_f (l ::: v ::: r ::: _) := IntvSets.Cons l v r;
      mod_fns mem_f (k ::: t ::: _) := IntvSets.mem k t;
      mod_fns contains_f (l ::: h ::: t ::: _) := IntvSets.contains l h t;
      mod_fns add_f (l ::: h ::: t ::: _) := IntvSets.add l h t;
      mod_fns remove_f (l ::: h ::: t ::: _) := IntvSets.remove l h t;
      mod_fns union_f (l ::: r ::: _) := IntvSets.union l r;
      mod_fns beq_f (l ::: r ::: _) := IntvSets.beq l r;
      mod_fns cond_t (t ::: l ::: r ::: _) := ite t l r;
      mod_fns cond_b (t ::: l ::: r ::: _) := ite t l r;
      mod_fns cond_z (t ::: l ::: r ::: _) := ite t l r;
      mod_fns b_and (l ::: r ::: _) :=  l && r;
      mod_fns b_or (l ::: r ::: _) := l || r;
    }.
  
  Equations mod_rels {params}
    (r: sig_rels sig params)
    (env: HList.t mod_sorts params) : Prop :=
    { 
      mod_rels lt_z (l ::: r ::: _) := (l < r)%Z;
      mod_rels le_z (l ::: r ::: _) := (l <= r)%Z;
      mod_rels gt_z (l ::: r ::: _) := (l > r)%Z;
      mod_rels in_r (x ::: t ::: _) := IntvSets.In x t;
      mod_rels ok_r (t ::: _) := IntvSets.ok' t;
    }.

  Arguments mod_fns _ _ _ _ : clear implicits.
  Arguments mod_rels _ _ _ : clear implicits.
  
  Definition intvset_model : model sig := {|
    FirstOrder.mod_sorts := mod_sorts;
    FirstOrder.mod_fns := mod_fns;
    FirstOrder.mod_rels := mod_rels;
  |}.
  (*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

  (*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)

  MetaCoq Quote Definition t_ite := @ite.
  MetaCoq Quote Definition t_zlt := @Z.ltb.
  MetaCoq Quote Definition t_zle := @Z.leb.
  MetaCoq Quote Definition t_zgt := @Z.gtb.
  MetaCoq Quote Definition t_zge := @Z.geb.
  MetaCoq Quote Definition t_zeq := @Z.eqb.
  MetaCoq Quote Definition t_zlt' := @Z.lt.
  MetaCoq Quote Definition t_zle' := @Z.le.
  MetaCoq Quote Definition t_zgt' := @Z.gt.
  MetaCoq Quote Definition t_nil := @Nil.
  MetaCoq Quote Definition t_cons := @Cons.
  MetaCoq Quote Definition t_zmax := @Z.max.
  MetaCoq Quote Definition t_zmin := @Z.min.
  MetaCoq Quote Definition t_mem := (@IntvSets.mem).
  MetaCoq Quote Definition t_contains := @IntvSets.contains.
  MetaCoq Quote Definition t_add := (@IntvSets.add).
  MetaCoq Quote Definition t_remove := @IntvSets.remove.
  MetaCoq Quote Definition t_union := (@IntvSets.union).
  MetaCoq Quote Definition t_beq := @IntvSets.beq.
  MetaCoq Quote Definition t_andb := @andb.
  MetaCoq Quote Definition t_orb := @orb. 
  MetaCoq Quote Definition t_in := (@IntvSets.In).
  MetaCoq Quote Definition t_ok := (@IntvSets.ok').
  
  Definition is_zlt t := eq_term t t_zlt.
  Definition is_zle t := eq_term t t_zle.
  Definition is_zgt t := eq_term t t_zgt.
  Definition is_zge t := eq_term t t_zge.
  Definition is_zeq t := eq_term t t_zeq.
  Definition is_zlt' t := eq_term t t_zlt'.
  Definition is_zle' t := eq_term t t_zle'.
  Definition is_zgt' t := eq_term t t_zgt'.
  Definition is_nil t := eq_term t t_nil.
  Definition is_cons t := eq_term t t_cons.
  Definition is_zmax t := eq_term t t_zmax.
  Definition is_zmin t := eq_term t t_zmin.
  Definition is_mem t := eq_ctor t t_mem.
  Definition is_contains t := eq_term t t_contains.
  Definition is_add t := eq_term t t_add.
  Definition is_remove t := eq_term t t_remove.
  Definition is_union t := eq_term t t_union.
  Definition is_beq t := eq_term t t_beq.
  Definition is_andb t := eq_term t t_andb.
  Definition is_orb t := eq_term t t_orb.
  Definition is_in t := eq_term t t_in.
  Definition is_ok t := eq_term t t_ok.

  MetaCoq Quote Definition t_bool := (bool).
  MetaCoq Quote Definition t_Z := (Z).
  MetaCoq Quote Definition t_T := (t).

  Definition is_cond_b t :=
    match t with 
    | tApp f (t :: _) => 
      andb (eq_term f t_ite) (eq_term t t_bool)
    | _ => false
    end.

  Definition is_cond_t t :=
    match t with 
    | tApp f (t :: _) => 
      andb (eq_term f t_ite) (eq_term t t_T)
    | _ => false
    end.

  Definition is_cond_z t :=
    match t with 
    | tApp f (t :: _) => 
      andb (eq_term f t_ite) (eq_term t t_Z)
    | _ => false
    end.

  Notation tac_bool := (tacLit sig intvset_model bool_lit (fun b => (BS; b)) (fun b _ => (BS; TFun sig (b_lit b) hnil))).
  Notation tac_fun f := (tacFun _ _ (Mk_fun_sym sig _ _ f)).
  Notation tac_rel f := (tacRel _ _ (Mk_rel_sym sig _ f)).

  Definition match_tacs : list ((term -> bool) * tac_syn sig intvset_model) := [
        (is_zlt, tac_fun z_lt )
      ; (is_zle, tac_fun z_le )
      ; (is_zgt, tac_fun z_gt )
      ; (is_zge, tac_fun z_ge )
      ; (is_zeq, tac_fun z_eqb )
      ; (is_nil, tac_fun nil_f )
      ; (is_cons, tac_fun cons_f )
      ; (is_zmax, tac_fun z_max )
      ; (is_zmin, tac_fun z_min )
      ; (is_mem, tac_fun mem_f )
      ; (is_contains, tac_fun contains_f )
      ; (is_add, tac_fun add_f )
      ; (is_remove, tac_fun remove_f )
      ; (is_union, tac_fun union_f )
      ; (is_beq, tac_fun beq_f )
      ; (is_andb, tac_fun b_and )
      ; (is_orb, tac_fun b_or )
      ; (is_cond_t, tac_fun cond_t )
      ; (is_cond_b, tac_fun cond_b )
      ; (is_cond_z, tac_fun cond_z )
      ; (is_zgt', tac_rel gt_z)
      ; (is_zle', tac_rel le_z)
      ; (is_zlt', tac_rel lt_z)
      ; (is_in, tac_rel in_r)
      ; (is_ok, tac_rel ok_r)
      ; ( is_bool_term, tac_bool )
  ].

  Definition match_inds : list ((term -> bool) * sorts) := [
      (eq_term t_T, TS)
    ; (eq_term t_bool, BS)
    ; (eq_term t_Z, ZS)
  ].
  Transparent denote_tm.

  Local Declare ML Module "mirrorsolve".
  RegisterSMTInd TS (SICases [
    ("cons"%string, [ 
      SISort (SInt tt); 
      SISort (SInt tt); 
      SIRec]); 
    ("nil"%string, [])
    ]) "Interval".
  (*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

  (*** MS BEGIN {"type": "configuration", "config_type":"plugin"} *)
  RegisterSMTSort ZS SInt.
  RegisterSMTSort BS SBool.

  RegisterSMTUF "min" ZS ZS ZS.
  RegisterSMTUF "max" ZS ZS ZS.
  RegisterSMTUF "mem" BS ZS TS.
  RegisterSMTUF "contains" BS ZS ZS TS.
  RegisterSMTUF "add" TS ZS ZS TS.
  RegisterSMTUF "remove" TS ZS ZS TS.
  RegisterSMTUF "intset_union" TS TS TS.
  (* RegisterSMTUF "beq" BS TS TS. *)
  RegisterSMTUF "in" BS ZS TS.
  RegisterSMTUF "ok" BS TS.

  RegisterSMTFun IntvSets.z_lt "<" 2.
  RegisterSMTFun IntvSets.z_gt ">" 2.
  RegisterSMTFun IntvSets.z_le "<=" 2.
  RegisterSMTFun IntvSets.z_ge ">=" 2.
  RegisterSMTFun IntvSets.z_eqb "=" 2.
  RegisterSMTFun IntvSets.lt_z "<" 2.
  RegisterSMTFun IntvSets.le_z "<=" 2.
  RegisterSMTFun IntvSets.gt_z ">" 2.
  RegisterSMTFun IntvSets.nil_f "nil" 0.
  RegisterSMTFun IntvSets.cons_f "cons" 3.
  RegisterSMTFun IntvSets.z_max "max" 2.
  RegisterSMTFun IntvSets.z_min "min" 2.
  RegisterSMTFun IntvSets.mem_f "mem" 2.
  RegisterSMTFun IntvSets.contains_f "contains" 3.
  RegisterSMTFun IntvSets.add_f "add" 3.
  RegisterSMTFun IntvSets.remove_f "remove" 3.
  RegisterSMTFun IntvSets.union_f "intset_union" 2.
  RegisterSMTFun IntvSets.beq_f "=" 2.
  RegisterSMTFun IntvSets.b_and "and" 2.
  RegisterSMTFun IntvSets.b_or "or" 2.
  RegisterSMTFun IntvSets.cond_b "ite" 3.
  RegisterSMTFun IntvSets.cond_t "ite" 3.
  RegisterSMTFun IntvSets.cond_z "ite" 3.
  RegisterSMTFun IntvSets.in_r "in" 2.
  RegisterSMTFun IntvSets.ok_r "ok" 1.

  RegisterSMTBuiltin IntvSets.b_lit BoolLit.
  (*** MS END {"type": "configuration", "config_type":"plugin"} *)

  (*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
  Transparent denote_tm.
  Require Import MirrorSolve.Axioms.

  Ltac check_goal_unsat := 
    match goal with 
    | |- ?G => check_unsat_neg G; eapply UnsoundAxioms.interp_true
    end.

  (*** MS END {"type": "configuration", "config_type":"boilerplate"} *)
  (*** MS BEGIN {"type": "configuration", "config_type":"tactics"} *)
  Lemma z_max_eq: 
    forall x y, Z.max x y = ite (Z.ltb x y) y x.
  Proof.
    intros.
    destruct (_ <? _)%Z eqn:?;
    simpl;
    lia.
  Qed.
  Lemma z_min_eq: 
    forall x y, Z.min x y = ite (Z.ltb x y) x y.
  Proof.
    intros.
    destruct (_ <? _)%Z eqn:?;
    simpl;
    lia.
  Qed.

  Ltac pose_intset_axioms := 
      Utils.pose_all (tt, IntvSets.in_nil, IntvSets.in_cons)
    ; Utils.pose_all (tt, IntvSets.ok'_nil, IntvSets.ok'_cons)
    ; Utils.pose_all (tt, IntvSets.mem_nil, IntvSets.mem_cons)
    ; Utils.pose_all (tt, IntvSets.contains_nil, IntvSets.contains_cons)
    ; Utils.pose_all (tt, IntvSets.add_nil, IntvSets.add_cons)
    ; Utils.pose_all (tt, IntvSets.remove_nil, IntvSets.remove_cons)
    ; Utils.pose_all (tt, IntvSets.union_nil_l, IntvSets.union_nil_r, IntvSets.union_cons_cons)
    ; Utils.pose_all (tt, IntvSets.beq_nil_nil, IntvSets.beq_nil_cons, IntvSets.beq_cons_nil, IntvSets.beq_cons_cons)
    ; Utils.pose_all (tt, IntvSets.z_max_eq, IntvSets.z_min_eq).
  
  Ltac prep_proof := pose_intset_axioms;
    unfold "<->" in *;
    Utils.revert_all;
    try (setoid_rewrite ok_ok').
  Ltac reflect t := reflect_goal sig intvset_model sorts_eq_dec match_tacs match_inds t.
  Ltac extract t := extract_goal sig intvset_model sorts_eq_dec match_tacs match_inds t.

  (*** MS END {"type": "configuration", "config_type":"tactics"} *)

  (*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
  MetaCoq Quote Definition mem_In_Nil := (
    
forall x : Z,
(forall (x0 l h : Z) (t : t),
 (l <= x0 < h \/ IntvSets.In x0 t -> IntvSets.In x0 (Cons l h t)) /\
 (IntvSets.In x0 (Cons l h t) -> l <= x0 < h \/ IntvSets.In x0 t)) ->
(forall z : Z, (IntvSets.In z Nil -> False) /\ (False -> IntvSets.In z Nil)) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x0 : Z, IntvSets.In x0 t -> h < x0) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x0 : Z, IntvSets.In x0 t -> h < x0) /\ ok' t)) ->
ok' Nil ->
(forall (x0 l h : Z) (t : t), mem x0 (Cons l h t) = ite (x0 <? h) (l <=? x0) (mem x0 t)) ->
(forall x0 : Z, mem x0 Nil = false) ->
(forall (L H5 l h : Z) (t : t), contains L H5 (Cons l h t) = (H5 <=? h) && (l <=? L) || contains L H5 t) ->
(forall x0 y : Z, contains x0 y Nil = false) ->
(forall (L H7 l h : Z) (s' : t),
 add L H7 (Cons l h s') =
 ite (h <? L) (Cons l h (add L H7 s')) (ite (H7 <? l) (Cons L H7 (Cons l h s')) (add (Z.min l L) (Z.max h H7) s'))) ->
(forall L H8 : Z, add L H8 Nil = Cons L H8 Nil) ->
(forall (L H9 l h : Z) (s' : t),
 IntvSets.remove L H9 (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H9 s'))
   (ite (H9 <? l) (Cons l h s')
      (ite (l <? L) (ite (H9 <? h) (Cons l L (Cons H9 h s')) (Cons l L (IntvSets.remove L H9 s')))
         (ite (H9 <? h) (Cons H9 h s') (IntvSets.remove L H9 s'))))) ->
(forall L H10 : Z, IntvSets.remove L H10 Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s1 : t, union s1 Nil = s1) ->
(forall s2 : t, union Nil s2 = s2) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H15 : Z) (s : t), beq (Cons L H15 s) Nil = false) ->
(forall (L H16 : Z) (s : t), beq Nil (Cons L H16 s) = false) ->
beq Nil Nil = true ->
(forall x0 y : Z, Z.min x0 y = ite (x0 <? y) x0 y) ->
(forall x0 y : Z, Z.max x0 y = ite (x0 <? y) y x0) ->
(mem x Nil = true -> IntvSets.In x Nil) /\ (IntvSets.In x Nil -> mem x Nil = true)

).
  MetaCoq Quote Definition mem_In_Cons := (
    forall (x l h : Z) (s : t),
l < h ->
(forall x0 : Z, IntvSets.In x0 s -> h < x0) ->
ok' s ->
(mem x s = true -> IntvSets.In x s) /\ (IntvSets.In x s -> mem x s = true) ->
(forall (x0 l0 h0 : Z) (t : t),
 (l0 <= x0 < h0 \/ IntvSets.In x0 t -> IntvSets.In x0 (Cons l0 h0 t)) /\
 (IntvSets.In x0 (Cons l0 h0 t) -> l0 <= x0 < h0 \/ IntvSets.In x0 t)) ->
(forall z : Z, (IntvSets.In z Nil -> False) /\ (False -> IntvSets.In z Nil)) ->
(forall (l0 h0 : Z) (t : t),
 (l0 < h0 /\ (forall x0 : Z, IntvSets.In x0 t -> h0 < x0) /\ ok' t -> ok' (Cons l0 h0 t)) /\
 (ok' (Cons l0 h0 t) -> l0 < h0 /\ (forall x0 : Z, IntvSets.In x0 t -> h0 < x0) /\ ok' t)) ->
ok' Nil ->
(forall (x0 l0 h0 : Z) (t : t), mem x0 (Cons l0 h0 t) = ite (x0 <? h0) (l0 <=? x0) (mem x0 t)) ->
(forall x0 : Z, mem x0 Nil = false) ->
(forall (L H l0 h0 : Z) (t : t), contains L H (Cons l0 h0 t) = (H <=? h0) && (l0 <=? L) || contains L H t) ->
(forall x0 y : Z, contains x0 y Nil = false) ->
(forall (L H l0 h0 : Z) (s' : t),
 add L H (Cons l0 h0 s') =
 ite (h0 <? L) (Cons l0 h0 (add L H s')) (ite (H <? l0) (Cons L H (Cons l0 h0 s')) (add (Z.min l0 L) (Z.max h0 H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l0 h0 : Z) (s' : t),
 IntvSets.remove L H (Cons l0 h0 s') =
 ite (h0 <? L) (Cons l0 h0 (IntvSets.remove L H s'))
   (ite (H <? l0) (Cons l0 h0 s')
      (ite (l0 <? L) (ite (H <? h0) (Cons l0 L (Cons H h0 s')) (Cons l0 L (IntvSets.remove L H s')))
         (ite (H <? h0) (Cons H h0 s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s1 : t, union s1 Nil = s1) ->
(forall s2 : t, union Nil s2 = s2) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s0 : t), beq (Cons L H s0) Nil = false) ->
(forall (L H : Z) (s0 : t), beq Nil (Cons L H s0) = false) ->
beq Nil Nil = true ->
(forall x0 y : Z, Z.min x0 y = ite (x0 <? y) x0 y) ->
(forall x0 y : Z, Z.max x0 y = ite (x0 <? y) y x0) ->
(mem x (Cons l h s) = true -> IntvSets.In x (Cons l h s)) /\ (IntvSets.In x (Cons l h s) -> mem x (Cons l h s) = true)
  ).
  (*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma mem_In:
    forall x s, 
      ok s -> 
      (mem x s = true <-> IntvSets.In x s).
  (*** MS END {"type": "proof_definition"} *)
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
    induction 1; 
    simpl.
  - intuition congruence.
  - destruct (Z.ltb x h) eqn:?.
  + destruct (Z.leb l x) eqn:?; 
    simpl.
    * intuition.
    * split; 
      intros. 
      congruence.
      exfalso. 
      destruct H0. 
      lia. 
      exploit BELOW; 
      eauto. 
      lia.
  + rewrite IHok. 
    intuition.
    (*** MS END {"type": "proof", "proof_type":"manual"} *)
    Restart.
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
    induction 1;
    try (erewrite ok_ok' in *).
    - hammer.
    - admit. (* hammer. *)
    Restart.
    (*** MS END {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
    induction 1;
    prep_proof.
    - reflect mem_In_Nil;
      check_goal_unsat.
    - reflect mem_In_Cons;
      check_goal_unsat.
      (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
  Qed.

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
  MetaCoq Quote Definition contains_In_Nil := (
    forall l0 h0 : Z,
l0 < h0 ->
(forall (x l h : Z) (t : t),
 (l <= x < h \/ IntvSets.In x t -> IntvSets.In x (Cons l h t)) /\
 (IntvSets.In x (Cons l h t) -> l <= x < h \/ IntvSets.In x t)) ->
(forall z : Z, (IntvSets.In z Nil -> False) /\ (False -> IntvSets.In z Nil)) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t)) ->
ok' Nil ->
(forall (x l h : Z) (t : t), mem x (Cons l h t) = ite (x <? h) (l <=? x) (mem x t)) ->
(forall x : Z, mem x Nil = false) ->
(forall (L H6 l h : Z) (t : t), contains L H6 (Cons l h t) = (H6 <=? h) && (l <=? L) || contains L H6 t) ->
(forall x y : Z, contains x y Nil = false) ->
(forall (L H8 l h : Z) (s' : t),
 add L H8 (Cons l h s') =
 ite (h <? L) (Cons l h (add L H8 s')) (ite (H8 <? l) (Cons L H8 (Cons l h s')) (add (Z.min l L) (Z.max h H8) s'))) ->
(forall L H9 : Z, add L H9 Nil = Cons L H9 Nil) ->
(forall (L H10 l h : Z) (s' : t),
 IntvSets.remove L H10 (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H10 s'))
   (ite (H10 <? l) (Cons l h s')
      (ite (l <? L) (ite (H10 <? h) (Cons l L (Cons H10 h s')) (Cons l L (IntvSets.remove L H10 s')))
         (ite (H10 <? h) (Cons H10 h s') (IntvSets.remove L H10 s'))))) ->
(forall L H11 : Z, IntvSets.remove L H11 Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s1 : t, union s1 Nil = s1) ->
(forall s2 : t, union Nil s2 = s2) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H16 : Z) (s : t), beq (Cons L H16 s) Nil = false) ->
(forall (L H17 : Z) (s : t), beq Nil (Cons L H17 s) = false) ->
beq Nil Nil = true ->
(forall x y : Z, Z.min x y = ite (x <? y) x y) ->
(forall x y : Z, Z.max x y = ite (x <? y) y x) ->
(false = true -> forall x : Z, l0 <= x < h0 -> False) /\ ((forall x : Z, l0 <= x < h0 -> False) -> false = true)
  ).

  MetaCoq Quote Definition contains_In_Cons_1 := (
    forall l0 h0 : Z,
l0 < h0 ->
forall (l h : Z) (s : t),
l < h ->
(forall x : Z, IntvSets.In x s -> h < x) ->
ok' s ->
(contains l0 h0 s = true -> forall x : Z, l0 <= x < h0 -> IntvSets.In x s) /\
((forall x : Z, l0 <= x < h0 -> IntvSets.In x s) -> contains l0 h0 s = true) ->
(h0 <=? h) = true ->
(l <=? l0) = true ->
(forall (x l1 h1 : Z) (t : t),
 (l1 <= x < h1 \/ IntvSets.In x t -> IntvSets.In x (Cons l1 h1 t)) /\
 (IntvSets.In x (Cons l1 h1 t) -> l1 <= x < h1 \/ IntvSets.In x t)) ->
(forall z : Z, (IntvSets.In z Nil -> False) /\ (False -> IntvSets.In z Nil)) ->
(forall (l1 h1 : Z) (t : t),
 (l1 < h1 /\ (forall x : Z, IntvSets.In x t -> h1 < x) /\ ok' t -> ok' (Cons l1 h1 t)) /\
 (ok' (Cons l1 h1 t) -> l1 < h1 /\ (forall x : Z, IntvSets.In x t -> h1 < x) /\ ok' t)) ->
ok' Nil ->
(forall (x l1 h1 : Z) (t : t), mem x (Cons l1 h1 t) = ite (x <? h1) (l1 <=? x) (mem x t)) ->
(forall x : Z, mem x Nil = false) ->
(forall (L H l1 h1 : Z) (t : t), contains L H (Cons l1 h1 t) = (H <=? h1) && (l1 <=? L) || contains L H t) ->
(forall x y : Z, contains x y Nil = false) ->
(forall (L H l1 h1 : Z) (s' : t),
 add L H (Cons l1 h1 s') =
 ite (h1 <? L) (Cons l1 h1 (add L H s')) (ite (H <? l1) (Cons L H (Cons l1 h1 s')) (add (Z.min l1 L) (Z.max h1 H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l1 h1 : Z) (s' : t),
 IntvSets.remove L H (Cons l1 h1 s') =
 ite (h1 <? L) (Cons l1 h1 (IntvSets.remove L H s'))
   (ite (H <? l1) (Cons l1 h1 s')
      (ite (l1 <? L) (ite (H <? h1) (Cons l1 L (Cons H h1 s')) (Cons l1 L (IntvSets.remove L H s')))
         (ite (H <? h1) (Cons H h1 s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s1 : t, union s1 Nil = s1) ->
(forall s2 : t, union Nil s2 = s2) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s0 : t), beq (Cons L H s0) Nil = false) ->
(forall (L H : Z) (s0 : t), beq Nil (Cons L H s0) = false) ->
beq Nil Nil = true ->
(forall x y : Z, Z.min x y = ite (x <? y) x y) ->
(forall x y : Z, Z.max x y = ite (x <? y) y x) ->
(true = true -> forall x : Z, l0 <= x < h0 -> l <= x < h \/ IntvSets.In x s) /\
((forall x : Z, l0 <= x < h0 -> l <= x < h \/ IntvSets.In x s) -> true = true)
).
MetaCoq Quote Definition contains_In_Cons_2 := (
    
forall l0 h0 : Z,
l0 < h0 ->
forall (l h : Z) (s : t),
l < h ->
(forall x : Z, IntvSets.In x s -> h < x) ->
ok' s ->
(contains l0 h0 s = true -> forall x : Z, l0 <= x < h0 -> IntvSets.In x s) /\
((forall x : Z, l0 <= x < h0 -> IntvSets.In x s) -> contains l0 h0 s = true) ->
(h0 <=? h) = true ->
(l <=? l0) = false ->
(forall (x l1 h1 : Z) (t : t),
 (l1 <= x < h1 \/ IntvSets.In x t -> IntvSets.In x (Cons l1 h1 t)) /\
 (IntvSets.In x (Cons l1 h1 t) -> l1 <= x < h1 \/ IntvSets.In x t)) ->
(forall z : Z, (IntvSets.In z Nil -> False) /\ (False -> IntvSets.In z Nil)) ->
(forall (l1 h1 : Z) (t : t),
 (l1 < h1 /\ (forall x : Z, IntvSets.In x t -> h1 < x) /\ ok' t -> ok' (Cons l1 h1 t)) /\
 (ok' (Cons l1 h1 t) -> l1 < h1 /\ (forall x : Z, IntvSets.In x t -> h1 < x) /\ ok' t)) ->
ok' Nil ->
(forall (x l1 h1 : Z) (t : t), mem x (Cons l1 h1 t) = ite (x <? h1) (l1 <=? x) (mem x t)) ->
(forall x : Z, mem x Nil = false) ->
(forall (L H l1 h1 : Z) (t : t), contains L H (Cons l1 h1 t) = (H <=? h1) && (l1 <=? L) || contains L H t) ->
(forall x y : Z, contains x y Nil = false) ->
(forall (L H l1 h1 : Z) (s' : t),
 add L H (Cons l1 h1 s') =
 ite (h1 <? L) (Cons l1 h1 (add L H s')) (ite (H <? l1) (Cons L H (Cons l1 h1 s')) (add (Z.min l1 L) (Z.max h1 H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l1 h1 : Z) (s' : t),
 IntvSets.remove L H (Cons l1 h1 s') =
 ite (h1 <? L) (Cons l1 h1 (IntvSets.remove L H s'))
   (ite (H <? l1) (Cons l1 h1 s')
      (ite (l1 <? L) (ite (H <? h1) (Cons l1 L (Cons H h1 s')) (Cons l1 L (IntvSets.remove L H s')))
         (ite (H <? h1) (Cons H h1 s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s1 : t, union s1 Nil = s1) ->
(forall s2 : t, union Nil s2 = s2) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s0 : t), beq (Cons L H s0) Nil = false) ->
(forall (L H : Z) (s0 : t), beq Nil (Cons L H s0) = false) ->
beq Nil Nil = true ->
(forall x y : Z, Z.min x y = ite (x <? y) x y) ->
(forall x y : Z, Z.max x y = ite (x <? y) y x) ->
(contains l0 h0 s = true -> forall x : Z, l0 <= x < h0 -> l <= x < h \/ IntvSets.In x s) /\
((forall x : Z, l0 <= x < h0 -> l <= x < h \/ IntvSets.In x s) -> contains l0 h0 s = true)
).
MetaCoq Quote Definition contains_In_Cons_3 := (
  forall l0 h0 : Z,
  l0 < h0 ->
  forall (l h : Z) (s : t),
  l < h ->
  (forall x : Z, IntvSets.In x s -> h < x) ->
  ok' s ->
  (contains l0 h0 s = true -> forall x : Z, l0 <= x < h0 -> IntvSets.In x s) /\
  ((forall x : Z, l0 <= x < h0 -> IntvSets.In x s) -> contains l0 h0 s = true) ->
  (h0 <=? h) = false ->
  (forall (x l1 h1 : Z) (t : t),
   (l1 <= x < h1 \/ IntvSets.In x t -> IntvSets.In x (Cons l1 h1 t)) /\
   (IntvSets.In x (Cons l1 h1 t) -> l1 <= x < h1 \/ IntvSets.In x t)) ->
  (forall z : Z, (IntvSets.In z Nil -> False) /\ (False -> IntvSets.In z Nil)) ->
  (forall (l1 h1 : Z) (t : t),
   (l1 < h1 /\ (forall x : Z, IntvSets.In x t -> h1 < x) /\ ok' t -> ok' (Cons l1 h1 t)) /\
   (ok' (Cons l1 h1 t) -> l1 < h1 /\ (forall x : Z, IntvSets.In x t -> h1 < x) /\ ok' t)) ->
  ok' Nil ->
  (forall (x l1 h1 : Z) (t : t), mem x (Cons l1 h1 t) = ite (x <? h1) (l1 <=? x) (mem x t)) ->
  (forall x : Z, mem x Nil = false) ->
  (forall (L H l1 h1 : Z) (t : t), contains L H (Cons l1 h1 t) = (H <=? h1) && (l1 <=? L) || contains L H t) ->
  (forall x y : Z, contains x y Nil = false) ->
  (forall (L H l1 h1 : Z) (s' : t),
   add L H (Cons l1 h1 s') =
   ite (h1 <? L) (Cons l1 h1 (add L H s')) (ite (H <? l1) (Cons L H (Cons l1 h1 s')) (add (Z.min l1 L) (Z.max h1 H) s'))) ->
  (forall L H : Z, add L H Nil = Cons L H Nil) ->
  (forall (L H l1 h1 : Z) (s' : t),
   IntvSets.remove L H (Cons l1 h1 s') =
   ite (h1 <? L) (Cons l1 h1 (IntvSets.remove L H s'))
     (ite (H <? l1) (Cons l1 h1 s')
        (ite (l1 <? L) (ite (H <? h1) (Cons l1 L (Cons H h1 s')) (Cons l1 L (IntvSets.remove L H s')))
           (ite (H <? h1) (Cons H h1 s') (IntvSets.remove L H s'))))) ->
  (forall L H : Z, IntvSets.remove L H Nil = Nil) ->
  (forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
  (forall s1 : t, union s1 Nil = s1) ->
  (forall s2 : t, union Nil s2 = s2) ->
  (forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
   beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
  (forall (L H : Z) (s0 : t), beq (Cons L H s0) Nil = false) ->
  (forall (L H : Z) (s0 : t), beq Nil (Cons L H s0) = false) ->
  beq Nil Nil = true ->
  (forall x y : Z, Z.min x y = ite (x <? y) x y) ->
  (forall x y : Z, Z.max x y = ite (x <? y) y x) ->
  (contains l0 h0 s = true -> forall x : Z, l0 <= x < h0 -> l <= x < h \/ IntvSets.In x s) /\
  ((forall x : Z, l0 <= x < h0 -> l <= x < h \/ IntvSets.In x s) -> contains l0 h0 s = true)
).
  (*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(*** MS BEGIN {"type": "proof_definition"} *)
Lemma contains_In:
  forall l0 h0, 
    l0 < h0 -> 
    forall s, ok s ->
  (contains l0 h0 s = true <-> (forall x, l0 <= x < h0 -> IntvSets.In x s)).
(*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  induction 2; 
  simpl.
- intuition.
- destruct (Z.leb h0 h) eqn:?; 
  simpl.
  destruct (Z.leb l l0) eqn:?; 
  simpl.
  intuition.
  rewrite IHok. 
  intuition. 
  destruct (H3 x); 
  auto. 
  exfalso.
  destruct (H3 l0).
  lia.
  lia.
  exploit BELOW; 
  eauto.
  lia.
  rewrite IHok.
  intuition.
  destruct (H3 x); 
  auto.
  exfalso.
  destruct (H3 h).
  lia.
  lia.
  exploit BELOW; 
  eauto.
  lia.
  Restart.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
    induction 2;
    try (erewrite ok_ok' in *).
    - hammer.
    - admit. (* hammer. *)
    Restart.
    (*** MS END {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":4} *)
  induction 2;
  simpl in *.
  prep_proof.
  - reflect contains_In_Nil;
    check_goal_unsat.
  - destruct (_ <=? _) eqn:?;
    simpl. 
    destruct (l <=? l0) eqn:?;
    simpl.
    all: prep_proof.
    + reflect contains_In_Cons_1;
      check_goal_unsat.
    + SetSMTSolver "z3".
      reflect contains_In_Cons_2;
      check_goal_unsat.
    + reflect contains_In_Cons_3;
      check_goal_unsat.
  (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":4} *)
Qed.

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition In_add_Nil := (
  forall x : Z,
(forall (x0 l h : Z) (t : t),
 (l <= x0 < h \/ IntvSets.In x0 t -> IntvSets.In x0 (Cons l h t)) /\
 (IntvSets.In x0 (Cons l h t) -> l <= x0 < h \/ IntvSets.In x0 t)) ->
(forall z : Z, (IntvSets.In z Nil -> False) /\ (False -> IntvSets.In z Nil)) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x0 : Z, IntvSets.In x0 t -> h < x0) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x0 : Z, IntvSets.In x0 t -> h < x0) /\ ok' t)) ->
ok' Nil ->
(forall (x0 l h : Z) (t : t), mem x0 (Cons l h t) = ite (x0 <? h) (l <=? x0) (mem x0 t)) ->
(forall x0 : Z, mem x0 Nil = false) ->
(forall (L H5 l h : Z) (t : t), contains L H5 (Cons l h t) = (H5 <=? h) && (l <=? L) || contains L H5 t) ->
(forall x0 y : Z, contains x0 y Nil = false) ->
(forall (L H7 l h : Z) (s' : t),
 add L H7 (Cons l h s') =
 ite (h <? L) (Cons l h (add L H7 s')) (ite (H7 <? l) (Cons L H7 (Cons l h s')) (add (Z.min l L) (Z.max h H7) s'))) ->
(forall L H8 : Z, add L H8 Nil = Cons L H8 Nil) ->
(forall (L H9 l h : Z) (s' : t),
 IntvSets.remove L H9 (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H9 s'))
   (ite (H9 <? l) (Cons l h s')
      (ite (l <? L) (ite (H9 <? h) (Cons l L (Cons H9 h s')) (Cons l L (IntvSets.remove L H9 s')))
         (ite (H9 <? h) (Cons H9 h s') (IntvSets.remove L H9 s'))))) ->
(forall L H10 : Z, IntvSets.remove L H10 Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s1 : t, union s1 Nil = s1) ->
(forall s2 : t, union Nil s2 = s2) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H15 : Z) (s : t), beq (Cons L H15 s) Nil = false) ->
(forall (L H16 : Z) (s : t), beq Nil (Cons L H16 s) = false) ->
beq Nil Nil = true ->
(forall x0 y : Z, Z.min x0 y = ite (x0 <? y) x0 y) ->
(forall x0 y : Z, Z.max x0 y = ite (x0 <? y) y x0) ->
ok' Nil ->
forall l0 h0 : Z,
(IntvSets.In x (add l0 h0 Nil) -> l0 <= x < h0 \/ IntvSets.In x Nil) /\
(l0 <= x < h0 \/ IntvSets.In x Nil -> IntvSets.In x (add l0 h0 Nil))
).

MetaCoq Quote Definition In_add_Cons := (
  forall (x lo hi : Z) (s : t),
(ok' s ->
 forall l0 h0 : Z,
 (IntvSets.In x (add l0 h0 s) -> l0 <= x < h0 \/ IntvSets.In x s) /\
 (l0 <= x < h0 \/ IntvSets.In x s -> IntvSets.In x (add l0 h0 s))) ->
(forall (x0 l h : Z) (t : t),
 (l <= x0 < h \/ IntvSets.In x0 t -> IntvSets.In x0 (Cons l h t)) /\
 (IntvSets.In x0 (Cons l h t) -> l <= x0 < h \/ IntvSets.In x0 t)) ->
(forall z : Z, (IntvSets.In z Nil -> False) /\ (False -> IntvSets.In z Nil)) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x0 : Z, IntvSets.In x0 t -> h < x0) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x0 : Z, IntvSets.In x0 t -> h < x0) /\ ok' t)) ->
ok' Nil ->
(forall (x0 l h : Z) (t : t), mem x0 (Cons l h t) = ite (x0 <? h) (l <=? x0) (mem x0 t)) ->
(forall x0 : Z, mem x0 Nil = false) ->
(forall (L H5 l h : Z) (t : t), contains L H5 (Cons l h t) = (H5 <=? h) && (l <=? L) || contains L H5 t) ->
(forall x0 y : Z, contains x0 y Nil = false) ->
(forall (L H7 l h : Z) (s' : t),
 add L H7 (Cons l h s') =
 ite (h <? L) (Cons l h (add L H7 s')) (ite (H7 <? l) (Cons L H7 (Cons l h s')) (add (Z.min l L) (Z.max h H7) s'))) ->
(forall L H8 : Z, add L H8 Nil = Cons L H8 Nil) ->
(forall (L H9 l h : Z) (s' : t),
 IntvSets.remove L H9 (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H9 s'))
   (ite (H9 <? l) (Cons l h s')
      (ite (l <? L) (ite (H9 <? h) (Cons l L (Cons H9 h s')) (Cons l L (IntvSets.remove L H9 s')))
         (ite (H9 <? h) (Cons H9 h s') (IntvSets.remove L H9 s'))))) ->
(forall L H10 : Z, IntvSets.remove L H10 Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s1 : t, union s1 Nil = s1) ->
(forall s2 : t, union Nil s2 = s2) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H15 : Z) (s0 : t), beq (Cons L H15 s0) Nil = false) ->
(forall (L H16 : Z) (s0 : t), beq Nil (Cons L H16 s0) = false) ->
beq Nil Nil = true ->
(forall x0 y : Z, Z.min x0 y = ite (x0 <? y) x0 y) ->
(forall x0 y : Z, Z.max x0 y = ite (x0 <? y) y x0) ->
ok' (Cons lo hi s) ->
forall l0 h0 : Z,
(IntvSets.In x (add l0 h0 (Cons lo hi s)) -> l0 <= x < h0 \/ IntvSets.In x (Cons lo hi s)) /\
(l0 <= x < h0 \/ IntvSets.In x (Cons lo hi s) -> IntvSets.In x (add l0 h0 (Cons lo hi s)))
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(*** MS BEGIN {"type": "proof_definition"} *)
Lemma In_add:
  forall x s, 
    ok s -> 
    forall l0 h0, 
      (IntvSets.In x (add l0 h0 s) <-> l0 <= x < h0 \/ IntvSets.In x s).
(*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  induction 1; 
  simpl; 
  intros.
  tauto.
  destruct (Z.ltb h l0) eqn:?;
  simpl. 
  rewrite IHok.
  tauto.
  destruct (Z.ltb h0 l) eqn:?;
  simpl.
  tauto.
  rewrite IHok.
  intuition.
  assert (l0 <= x < h0 \/ l <= x < h) by extlia.
  tauto.
  Restart.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
Proof.
    intros.
    erewrite ok_ok' in *.
    Utils.revert_all.
    (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
    induction s.
    - hammer.
    - admit. (* hammer. *)
    Restart.
    (*** MS END {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
Proof.
  intros;
  erewrite ok_ok' in *;
  Utils.revert_all.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
  induction s;
  prep_proof.
  - admit. (* reflect In_add_Nil;
    check_goal_unsat. *)
  - reflect In_add_Cons;
    check_goal_unsat.
  (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
Admitted.

(*** MS BEGIN {"type": "configuration", "config_type":"tactics"} *)
Ltac prep_proof' := pose proof In_add;
  prep_proof.
(*** MS END {"type": "configuration", "config_type":"tactics"} *)

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition add_ok_Nil := (
  (forall (x : Z) (s : t),
 ok' s ->
 forall l0 h0 : Z,
 (IntvSets.In x (add l0 h0 s) -> l0 <= x < h0 \/ IntvSets.In x s) /\
 (l0 <= x < h0 \/ IntvSets.In x s -> IntvSets.In x (add l0 h0 s))) ->
(forall (x l h : Z) (t : t),
 (l <= x < h \/ IntvSets.In x t -> IntvSets.In x (Cons l h t)) /\
 (IntvSets.In x (Cons l h t) -> l <= x < h \/ IntvSets.In x t)) ->
(forall z : Z, ~ IntvSets.In z Nil) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t)) ->
ok' Nil ->
(forall (x l h : Z) (t : t), mem x (Cons l h t) = ite (x <? h) (l <=? x) (mem x t)) ->
(forall x : Z, mem x Nil = false) ->
(forall (L H l h : Z) (t : t), contains L H (Cons l h t) = (H <=? h) && (l <=? L) || contains L H t) ->
(forall x y : Z, contains x y Nil = false) ->
(forall (L H l h : Z) (s' : t),
 add L H (Cons l h s') =
 ite (h <? L) (Cons l h (add L H s'))
   (ite (H <? l) (Cons L H (Cons l h s')) (add (Z.min l L) (Z.max h H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l h : Z) (s' : t),
 IntvSets.remove L H (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H s'))
   (ite (H <? l) (Cons l h s')
      (ite (l <? L) (ite (H <? h) (Cons l L (Cons H h s')) (Cons l L (IntvSets.remove L H s')))
         (ite (H <? h) (Cons H h s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t),
 union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s1 : t, union s1 Nil = s1) ->
(forall s2 : t, union Nil s2 = s2) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s : t), beq (Cons L H s) Nil = false) ->
(forall (L H : Z) (s : t), beq Nil (Cons L H s) = false) ->
beq Nil Nil = true ->
(forall x y : Z, Z.min x y = ite (x <? y) x y) ->
(forall x y : Z, Z.max x y = ite (x <? y) y x) ->
ok' Nil -> forall l0 h0 : Z, l0 < h0 -> ok' (add l0 h0 Nil)
).

MetaCoq Quote Definition add_ok_Cons := (
  forall (lo hi : Z) (s : t),
(ok' s -> forall l0 h0 : Z, l0 < h0 -> ok' (add l0 h0 s)) ->
(forall (x : Z) (s0 : t),
 ok' s0 ->
 forall l0 h0 : Z,
 (IntvSets.In x (add l0 h0 s0) -> l0 <= x < h0 \/ IntvSets.In x s0) /\
 (l0 <= x < h0 \/ IntvSets.In x s0 -> IntvSets.In x (add l0 h0 s0))) ->
(forall (x l h : Z) (t : t),
 (l <= x < h \/ IntvSets.In x t -> IntvSets.In x (Cons l h t)) /\
 (IntvSets.In x (Cons l h t) -> l <= x < h \/ IntvSets.In x t)) ->
(forall z : Z, ~ IntvSets.In z Nil) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t)) ->
ok' Nil ->
(forall (x l h : Z) (t : t), mem x (Cons l h t) = ite (x <? h) (l <=? x) (mem x t)) ->
(forall x : Z, mem x Nil = false) ->
(forall (L H6 l h : Z) (t : t), contains L H6 (Cons l h t) = (H6 <=? h) && (l <=? L) || contains L H6 t) ->
(forall x y : Z, contains x y Nil = false) ->
(forall (L H8 l h : Z) (s' : t),
 add L H8 (Cons l h s') =
 ite (h <? L) (Cons l h (add L H8 s')) (ite (H8 <? l) (Cons L H8 (Cons l h s')) (add (Z.min l L) (Z.max h H8) s'))) ->
(forall L H9 : Z, add L H9 Nil = Cons L H9 Nil) ->
(forall (L H10 l h : Z) (s' : t),
 IntvSets.remove L H10 (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H10 s'))
   (ite (H10 <? l) (Cons l h s')
      (ite (l <? L) (ite (H10 <? h) (Cons l L (Cons H10 h s')) (Cons l L (IntvSets.remove L H10 s')))
         (ite (H10 <? h) (Cons H10 h s') (IntvSets.remove L H10 s'))))) ->
(forall L H11 : Z, IntvSets.remove L H11 Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t),
 union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s1 : t, union s1 Nil = s1) ->
(forall s2 : t, union Nil s2 = s2) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H16 : Z) (s0 : t), beq (Cons L H16 s0) Nil = false) ->
(forall (L H17 : Z) (s0 : t), beq Nil (Cons L H17 s0) = false) ->
beq Nil Nil = true ->
(forall x y : Z, Z.min x y = ite (x <? y) x y) ->
(forall x y : Z, Z.max x y = ite (x <? y) y x) ->
ok' (Cons lo hi s) -> forall l0 h0 : Z, l0 < h0 -> ok' (add l0 h0 (Cons lo hi s))
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(*** MS BEGIN {"type": "proof_definition"} *)
Lemma add_ok:
  forall s, 
    ok s -> 
    forall l0 h0, 
      l0 < h0 -> 
      ok (add l0 h0 s).
(*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  induction 1; 
  simpl; 
  intros.
  constructor. 
  auto. 
  intros. 
  inv H0. 
  constructor.
  destruct (Z.ltb h l0) eqn:?.
  constructor; 
  auto.
  intros.
  rewrite In_add in H1; 
  auto.
  destruct H1. 
  lia. 
  auto.
  destruct (Z.ltb h0 l) eqn:?.
  constructor.
  auto.
  simpl; 
  intros.
  destruct H1.
  lia.
  exploit BELOW; 
  eauto.
  lia.
  constructor.
  lia.
  auto.
  auto.
  apply IHok.
  extlia.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  intros.
  erewrite ok_ok' in *.
  Utils.revert_all.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
  induction s.
  - admit. (* hammer. *) (* this one succeeds *)
  - admit. (* hammer. *)
  Restart.
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
Proof.
  intros;
  erewrite ok_ok' in *;
  Utils.revert_all.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
  induction s;
  prep_proof'.
  - admit. (* reflect add_ok_Nil;
    check_goal_unsat. *)
  - admit. (* reflect add_ok_Cons;
    check_goal_unsat. *)
(*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
Admitted.

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition In_remove_Nil := (
  
forall x l0 h0 : Z,
(forall (x0 : Z) (s : t),
 ok' s ->
 forall l1 h1 : Z,
 (IntvSets.In x0 (add l1 h1 s) -> l1 <= x0 < h1 \/ IntvSets.In x0 s) /\
 (l1 <= x0 < h1 \/ IntvSets.In x0 s -> IntvSets.In x0 (add l1 h1 s))) ->
(forall (x0 l h : Z) (t : t),
 (l <= x0 < h \/ IntvSets.In x0 t -> IntvSets.In x0 (Cons l h t)) /\
 (IntvSets.In x0 (Cons l h t) -> l <= x0 < h \/ IntvSets.In x0 t)) ->
(forall z : Z, ~ IntvSets.In z Nil) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x0 : Z, IntvSets.In x0 t -> h < x0) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x0 : Z, IntvSets.In x0 t -> h < x0) /\ ok' t)) ->
ok' Nil ->
(forall (x0 l h : Z) (t : t), mem x0 (Cons l h t) = ite (x0 <? h) (l <=? x0) (mem x0 t)) ->
(forall x0 : Z, mem x0 Nil = false) ->
(forall (L H l h : Z) (t : t), contains L H (Cons l h t) = (H <=? h) && (l <=? L) || contains L H t) ->
(forall x0 y : Z, contains x0 y Nil = false) ->
(forall (L H l h : Z) (s' : t),
 add L H (Cons l h s') =
 ite (h <? L) (Cons l h (add L H s'))
   (ite (H <? l) (Cons L H (Cons l h s')) (add (Z.min l L) (Z.max h H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l h : Z) (s' : t),
 IntvSets.remove L H (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H s'))
   (ite (H <? l) (Cons l h s')
      (ite (l <? L) (ite (H <? h) (Cons l L (Cons H h s')) (Cons l L (IntvSets.remove L H s')))
         (ite (H <? h) (Cons H h s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t),
 union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s1 : t, union s1 Nil = s1) ->
(forall s2 : t, union Nil s2 = s2) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s : t), beq (Cons L H s) Nil = false) ->
(forall (L H : Z) (s : t), beq Nil (Cons L H s) = false) ->
beq Nil Nil = true ->
(forall x0 y : Z, Z.min x0 y = ite (x0 <? y) x0 y) ->
(forall x0 y : Z, Z.max x0 y = ite (x0 <? y) y x0) ->
ok' Nil ->
(IntvSets.In x (IntvSets.remove l0 h0 Nil) -> ~ l0 <= x < h0 /\ IntvSets.In x Nil) /\
(~ l0 <= x < h0 /\ IntvSets.In x Nil -> IntvSets.In x (IntvSets.remove l0 h0 Nil))
).

MetaCoq Quote Definition In_remove_Cons := (
  forall (x l0 h0 lo hi : Z) (s : t),
(ok' s ->
 (IntvSets.In x (IntvSets.remove l0 h0 s) -> ~ l0 <= x < h0 /\ IntvSets.In x s) /\
 (~ l0 <= x < h0 /\ IntvSets.In x s -> IntvSets.In x (IntvSets.remove l0 h0 s))) ->
(forall (x0 : Z) (s0 : t),
 ok' s0 ->
 forall l1 h1 : Z,
 (IntvSets.In x0 (add l1 h1 s0) -> l1 <= x0 < h1 \/ IntvSets.In x0 s0) /\
 (l1 <= x0 < h1 \/ IntvSets.In x0 s0 -> IntvSets.In x0 (add l1 h1 s0))) ->
(forall (x0 l h : Z) (t : t),
 (l <= x0 < h \/ IntvSets.In x0 t -> IntvSets.In x0 (Cons l h t)) /\
 (IntvSets.In x0 (Cons l h t) -> l <= x0 < h \/ IntvSets.In x0 t)) ->
(forall z : Z, ~ IntvSets.In z Nil) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x0 : Z, IntvSets.In x0 t -> h < x0) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x0 : Z, IntvSets.In x0 t -> h < x0) /\ ok' t)) ->
ok' Nil ->
(forall (x0 l h : Z) (t : t), mem x0 (Cons l h t) = ite (x0 <? h) (l <=? x0) (mem x0 t)) ->
(forall x0 : Z, mem x0 Nil = false) ->
(forall (L H l h : Z) (t : t), contains L H (Cons l h t) = (H <=? h) && (l <=? L) || contains L H t) ->
(forall x0 y : Z, contains x0 y Nil = false) ->
(forall (L H l h : Z) (s' : t),
 add L H (Cons l h s') =
 ite (h <? L) (Cons l h (add L H s'))
   (ite (H <? l) (Cons L H (Cons l h s')) (add (Z.min l L) (Z.max h H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l h : Z) (s' : t),
 IntvSets.remove L H (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H s'))
   (ite (H <? l) (Cons l h s')
      (ite (l <? L) (ite (H <? h) (Cons l L (Cons H h s')) (Cons l L (IntvSets.remove L H s')))
         (ite (H <? h) (Cons H h s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t),
 union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s1 : t, union s1 Nil = s1) ->
(forall s2 : t, union Nil s2 = s2) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s0 : t), beq (Cons L H s0) Nil = false) ->
(forall (L H : Z) (s0 : t), beq Nil (Cons L H s0) = false) ->
beq Nil Nil = true ->
(forall x0 y : Z, Z.min x0 y = ite (x0 <? y) x0 y) ->
(forall x0 y : Z, Z.max x0 y = ite (x0 <? y) y x0) ->
ok' (Cons lo hi s) ->
(IntvSets.In x (IntvSets.remove l0 h0 (Cons lo hi s)) -> ~ l0 <= x < h0 /\ IntvSets.In x (Cons lo hi s)) /\
(~ l0 <= x < h0 /\ IntvSets.In x (Cons lo hi s) -> IntvSets.In x (IntvSets.remove l0 h0 (Cons lo hi s)))
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(*** MS BEGIN {"type": "proof_definition"} *)
Lemma In_remove:
  forall x l0 h0 s, 
    ok s ->
    (IntvSets.In x (IntvSets.remove l0 h0 s) <-> ~(l0 <= x < h0) /\ IntvSets.In x s).
(*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  induction 1; 
  simpl.
  tauto.
  destruct (Z.ltb h l0) eqn:?;
  simpl. 
  rewrite IHok. 
  intuition lia.
  destruct (Z.ltb h0 l) eqn:?.
  simpl. 
  intuition. 
  exploit BELOW;
  eauto. 
  lia.
  destruct (Z.ltb l l0) eqn:?.
  destruct (Z.ltb h0 h) eqn:?; 
  simpl. 
  clear IHok. 
  split.
  intros [A | [A | A]].
  split. 
  lia. 
  left; 
  lia.
  split. 
  lia. 
  left; 
  lia.
  split. 
  exploit BELOW; 
  eauto. 
  lia. 
  auto.
  intros [A [B | B]].
  destruct (Z.ltb x l0) eqn:?. 
  left; 
  lia. 
  right; 
  left; 
  lia.
  auto.
  intuition lia.
  destruct (Z.ltb h0 h) eqn:?; 
  simpl.
  intuition. 
  exploit BELOW;
  eauto. 
  lia.
  rewrite IHok. 
  intuition.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  intros.
  erewrite ok_ok' in *.
  Utils.revert_all.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
  induction s.
  - admit. (* hammer. *) (* success *)
  - admit. (* hammer. *)
  Restart.
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
Proof.
  intros;
  erewrite ok_ok' in *;
  Utils.revert_all.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
  induction s;
  prep_proof'.
  - reflect In_remove_Nil;
    check_goal_unsat.
  - reflect In_remove_Cons;
    check_goal_unsat.
(*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
Qed.

(*** MS BEGIN {"type": "configuration", "config_type":"tactics"} *)
Ltac prep_proof'' := pose proof In_remove;
  prep_proof'.
(*** MS END {"type": "configuration", "config_type":"tactics"} *)


(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition remove_ok_Nil := (
  
forall l0 h0 : Z,
l0 < h0 ->
(forall (x l1 h1 : Z) (s : t),
 ok' s ->
 (IntvSets.In x (IntvSets.remove l1 h1 s) -> ~ l1 <= x < h1 /\ IntvSets.In x s) /\
 (~ l1 <= x < h1 /\ IntvSets.In x s -> IntvSets.In x (IntvSets.remove l1 h1 s))) ->
(forall (x : Z) (s : t),
 ok' s ->
 forall l1 h1 : Z,
 (IntvSets.In x (add l1 h1 s) -> l1 <= x < h1 \/ IntvSets.In x s) /\
 (l1 <= x < h1 \/ IntvSets.In x s -> IntvSets.In x (add l1 h1 s))) ->
(forall (x l h : Z) (t : t),
 (l <= x < h \/ IntvSets.In x t -> IntvSets.In x (Cons l h t)) /\
 (IntvSets.In x (Cons l h t) -> l <= x < h \/ IntvSets.In x t)) ->
(forall z : Z, ~ IntvSets.In z Nil) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t)) ->
ok' Nil ->
(forall (x l h : Z) (t : t), mem x (Cons l h t) = ite (x <? h) (l <=? x) (mem x t)) ->
(forall x : Z, mem x Nil = false) ->
(forall (L H l h : Z) (t : t), contains L H (Cons l h t) = (H <=? h) && (l <=? L) || contains L H t) ->
(forall x y : Z, contains x y Nil = false) ->
(forall (L H l h : Z) (s' : t),
 add L H (Cons l h s') =
 ite (h <? L) (Cons l h (add L H s')) (ite (H <? l) (Cons L H (Cons l h s')) (add (Z.min l L) (Z.max h H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l h : Z) (s' : t),
 IntvSets.remove L H (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H s'))
   (ite (H <? l) (Cons l h s')
      (ite (l <? L) (ite (H <? h) (Cons l L (Cons H h s')) (Cons l L (IntvSets.remove L H s')))
         (ite (H <? h) (Cons H h s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s1 : t, union s1 Nil = s1) ->
(forall s2 : t, union Nil s2 = s2) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s : t), beq (Cons L H s) Nil = false) ->
(forall (L H : Z) (s : t), beq Nil (Cons L H s) = false) ->
beq Nil Nil = true ->
(forall x y : Z, Z.min x y = ite (x <? y) x y) ->
(forall x y : Z, Z.max x y = ite (x <? y) y x) -> ok' Nil -> ok' (IntvSets.remove l0 h0 Nil)
).

MetaCoq Quote Definition remove_ok_Cons := (
  forall l0 h0 : Z,
l0 < h0 ->
forall (lo hi : Z) (s : t),
(ok' s -> ok' (IntvSets.remove l0 h0 s)) ->
(forall (x l1 h1 : Z) (s0 : t),
 ok' s0 ->
 (IntvSets.In x (IntvSets.remove l1 h1 s0) -> ~ l1 <= x < h1 /\ IntvSets.In x s0) /\
 (~ l1 <= x < h1 /\ IntvSets.In x s0 -> IntvSets.In x (IntvSets.remove l1 h1 s0))) ->
(forall (x : Z) (s0 : t),
 ok' s0 ->
 forall l1 h1 : Z,
 (IntvSets.In x (add l1 h1 s0) -> l1 <= x < h1 \/ IntvSets.In x s0) /\
 (l1 <= x < h1 \/ IntvSets.In x s0 -> IntvSets.In x (add l1 h1 s0))) ->
(forall (x l h : Z) (t : t),
 (l <= x < h \/ IntvSets.In x t -> IntvSets.In x (Cons l h t)) /\
 (IntvSets.In x (Cons l h t) -> l <= x < h \/ IntvSets.In x t)) ->
(forall z : Z, ~ IntvSets.In z Nil) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t)) ->
ok' Nil ->
(forall (x l h : Z) (t : t), mem x (Cons l h t) = ite (x <? h) (l <=? x) (mem x t)) ->
(forall x : Z, mem x Nil = false) ->
(forall (L H l h : Z) (t : t), contains L H (Cons l h t) = (H <=? h) && (l <=? L) || contains L H t) ->
(forall x y : Z, contains x y Nil = false) ->
(forall (L H l h : Z) (s' : t),
 add L H (Cons l h s') =
 ite (h <? L) (Cons l h (add L H s')) (ite (H <? l) (Cons L H (Cons l h s')) (add (Z.min l L) (Z.max h H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l h : Z) (s' : t),
 IntvSets.remove L H (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H s'))
   (ite (H <? l) (Cons l h s')
      (ite (l <? L) (ite (H <? h) (Cons l L (Cons H h s')) (Cons l L (IntvSets.remove L H s')))
         (ite (H <? h) (Cons H h s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s1 : t, union s1 Nil = s1) ->
(forall s2 : t, union Nil s2 = s2) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s0 : t), beq (Cons L H s0) Nil = false) ->
(forall (L H : Z) (s0 : t), beq Nil (Cons L H s0) = false) ->
beq Nil Nil = true ->
(forall x y : Z, Z.min x y = ite (x <? y) x y) ->
(forall x y : Z, Z.max x y = ite (x <? y) y x) -> ok' (Cons lo hi s) -> ok' (IntvSets.remove l0 h0 (Cons lo hi s))
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(*** MS BEGIN {"type": "configuration", "config_type":"plugin"} *)
SetSMTSolver "z3".
(*** MS END {"type": "configuration", "config_type":"plugin"} *)

(*** MS BEGIN {"type": "proof_definition"} *)
Lemma remove_ok:
  forall l0 h0, 
    l0 < h0 -> 
      forall s, 
        ok s -> 
        ok (IntvSets.remove l0 h0 s).
(*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  induction 2; 
  simpl.
  constructor.
  destruct (Z.ltb h l0) eqn:?.
  constructor; 
  auto. 
  intros; 
  apply BELOW.
  rewrite In_remove in H1;
  tauto.
  destruct (Z.ltb h0 l) eqn:?.
  constructor;
  auto.
  destruct (Z.ltb l l0) eqn:?.
  destruct (Z.ltb h0 h) eqn:?.
  constructor.
  lia.
  intros.
  inv H1.
  lia.
  exploit BELOW;
  eauto.
  lia.
  constructor.
  lia.
  auto.
  auto.
  constructor; 
  lia || auto.
  intros. 
  rewrite In_remove in H1 by auto. 
  destruct H1. 
  exploit BELOW; 
  eauto. 
  lia.
  destruct (Z.ltb h0 h) eqn:?.
  constructor; 
  lia || auto.
  auto.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  intros.
  erewrite ok_ok' in *.
  Utils.revert_all.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
  induction s.
  - hammer.
  - admit. (* hammer. *)
  Restart.
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
Proof.
  intros;
  erewrite ok_ok' in *;
  Utils.revert_all.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
  induction s;
  prep_proof''.
  - reflect remove_ok_Nil;
    check_goal_unsat.
  - reflect remove_ok_Cons;
    check_goal_unsat.
(*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
Qed.

(* Lemma In_inter:
  forall x s1, ok s1 -> forall s2, ok s2 ->
  (IntvSets.In x (inter s1 s2) <-> IntvSets.In x s1 /\ IntvSets.In x s2).
Proof.
  induction 1.
  simpl. induction 1; simpl. tauto. tauto.
  assert (ok (Cons l h s)) by (constructor; auto).
  induction 1; simpl.
  tauto.
  assert (ok (Cons l0 h0 s0)) by (constructor; auto).
  destruct (zle h l0).
  rewrite IHok; auto. simpl. intuition.
  destruct H3; eauto; intuition.
  exploit BELOW0; eauto. intros. extlia.
  shelve.
  destruct (zle h0 l).
  simpl in IHok0; rewrite IHok0. intuition. extlia.
  exploit BELOW; eauto. intros; extlia.
  destruct (zle l l0).
  destruct (zle h0 h).
  simpl. simpl in IHok0; rewrite IHok0. intuition.
  simpl. rewrite IHok; auto. simpl. intuition.  exploit BELOW0; eauto. intros; extlia.
  destruct (zle h h0).
  simpl. rewrite IHok; auto. simpl. intuition.
  simpl. simpl in IHok0; rewrite IHok0. intuition.
  exploit BELOW; eauto. intros; extlia.
Qed. *)

(* Lemma inter_ok:
  forall s1, ok s1 -> forall s2, ok s2 -> ok (inter s1 s2).
Proof.
  induction 1.
  intros; simpl. destruct s2; constructor.
  assert (ok (Cons l h s)). constructor; auto.
  induction 1; simpl.
  constructor.
  assert (ok (Cons l0 h0 s0)). constructor; auto.
  destruct (zle h l0).
  auto.
  destruct (zle h0 l).
  auto.
  destruct (zle l l0).
  destruct (zle h0 h).
  constructor; auto. intros.
  assert (In x (inter (Cons l h s) s0)) by exact H3.
  rewrite In_inter in H4; auto. apply BELOW0. tauto.
  constructor. lia. intros. rewrite In_inter in H3; auto. apply BELOW. tauto.
  auto.
  destruct (zle h h0).
  constructor. lia. intros. rewrite In_inter in H3; auto. apply BELOW. tauto.
  auto.
  constructor. lia. intros.
  assert (In x (inter (Cons l h s) s0)) by exact H3.
  rewrite In_inter in H4; auto. apply BELOW0. tauto.
  auto.
Qed. *)

(*** MS BEGIN {"type": "configuration", "config_type":"tactics"} *)
Ltac prep_proof''' := pose proof add_ok;
  prep_proof''.
(*** MS END {"type": "configuration", "config_type":"tactics"} *)


(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition In_ok_union_Nil_Nil := (
  
ok' Nil ->
forall s2 : t,
s2 = Nil ->
(forall s : t, ok' s -> forall l0 h0 : Z, l0 < h0 -> ok' (add l0 h0 s)) ->
(forall (x l0 h0 : Z) (s : t),
 ok' s ->
 (IntvSets.In x (IntvSets.remove l0 h0 s) -> ~ l0 <= x < h0 /\ IntvSets.In x s) /\
 (~ l0 <= x < h0 /\ IntvSets.In x s -> IntvSets.In x (IntvSets.remove l0 h0 s))) ->
(forall (x : Z) (s : t),
 ok' s ->
 forall l0 h0 : Z,
 (IntvSets.In x (add l0 h0 s) -> l0 <= x < h0 \/ IntvSets.In x s) /\
 (l0 <= x < h0 \/ IntvSets.In x s -> IntvSets.In x (add l0 h0 s))) ->
(forall (x l h : Z) (t : t),
 (l <= x < h \/ IntvSets.In x t -> IntvSets.In x (Cons l h t)) /\
 (IntvSets.In x (Cons l h t) -> l <= x < h \/ IntvSets.In x t)) ->
(forall z : Z, ~ IntvSets.In z Nil) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t)) ->
ok' Nil ->
(forall (x l h : Z) (t : t), mem x (Cons l h t) = ite (x <? h) (l <=? x) (mem x t)) ->
(forall x : Z, mem x Nil = false) ->
(forall (L H l h : Z) (t : t), contains L H (Cons l h t) = (H <=? h) && (l <=? L) || contains L H t) ->
(forall x y : Z, contains x y Nil = false) ->
(forall (L H l h : Z) (s' : t),
 add L H (Cons l h s') =
 ite (h <? L) (Cons l h (add L H s')) (ite (H <? l) (Cons L H (Cons l h s')) (add (Z.min l L) (Z.max h H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l h : Z) (s' : t),
 IntvSets.remove L H (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H s'))
   (ite (H <? l) (Cons l h s')
      (ite (l <? L) (ite (H <? h) (Cons l L (Cons H h s')) (Cons l L (IntvSets.remove L H s')))
         (ite (H <? h) (Cons H h s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t),
 union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s1 : t, union s1 Nil = s1) ->
(forall s3 : t, union Nil s3 = s3) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s : t), beq (Cons L H s) Nil = false) ->
(forall (L H : Z) (s : t), beq Nil (Cons L H s) = false) ->
beq Nil Nil = true ->
(forall x y : Z, Z.min x y = ite (x <? y) x y) ->
(forall x y : Z, Z.max x y = ite (x <? y) y x) ->
ok' Nil ->
ok' (union Nil Nil) /\
(forall x : Z,
 (IntvSets.In x Nil \/ IntvSets.In x Nil -> IntvSets.In x (union Nil Nil)) /\
 (IntvSets.In x (union Nil Nil) -> IntvSets.In x Nil \/ IntvSets.In x Nil))
).

MetaCoq Quote Definition In_ok_union_Nil_Cons := (
  ok' Nil ->
forall (s2 : t) (lo hi : Z) (t0 : t),
s2 = Cons lo hi t0 ->
(forall s : t, ok' s -> forall l0 h0 : Z, l0 < h0 -> ok' (add l0 h0 s)) ->
(forall (x l0 h0 : Z) (s : t),
 ok' s ->
 (IntvSets.In x (IntvSets.remove l0 h0 s) -> ~ l0 <= x < h0 /\ IntvSets.In x s) /\
 (~ l0 <= x < h0 /\ IntvSets.In x s -> IntvSets.In x (IntvSets.remove l0 h0 s))) ->
(forall (x : Z) (s : t),
 ok' s ->
 forall l0 h0 : Z,
 (IntvSets.In x (add l0 h0 s) -> l0 <= x < h0 \/ IntvSets.In x s) /\
 (l0 <= x < h0 \/ IntvSets.In x s -> IntvSets.In x (add l0 h0 s))) ->
(forall (x l h : Z) (t : t),
 (l <= x < h \/ IntvSets.In x t -> IntvSets.In x (Cons l h t)) /\
 (IntvSets.In x (Cons l h t) -> l <= x < h \/ IntvSets.In x t)) ->
(forall z : Z, ~ IntvSets.In z Nil) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t)) ->
ok' Nil ->
(forall (x l h : Z) (t : t), mem x (Cons l h t) = ite (x <? h) (l <=? x) (mem x t)) ->
(forall x : Z, mem x Nil = false) ->
(forall (L H l h : Z) (t : t), contains L H (Cons l h t) = (H <=? h) && (l <=? L) || contains L H t) ->
(forall x y : Z, contains x y Nil = false) ->
(forall (L H l h : Z) (s' : t),
 add L H (Cons l h s') =
 ite (h <? L) (Cons l h (add L H s')) (ite (H <? l) (Cons L H (Cons l h s')) (add (Z.min l L) (Z.max h H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l h : Z) (s' : t),
 IntvSets.remove L H (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H s'))
   (ite (H <? l) (Cons l h s')
      (ite (l <? L) (ite (H <? h) (Cons l L (Cons H h s')) (Cons l L (IntvSets.remove L H s')))
         (ite (H <? h) (Cons H h s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t),
 union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s1 : t, union s1 Nil = s1) ->
(forall s3 : t, union Nil s3 = s3) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s : t), beq (Cons L H s) Nil = false) ->
(forall (L H : Z) (s : t), beq Nil (Cons L H s) = false) ->
beq Nil Nil = true ->
(forall x y : Z, Z.min x y = ite (x <? y) x y) ->
(forall x y : Z, Z.max x y = ite (x <? y) y x) ->
ok' (Cons lo hi t0) ->
ok' (union Nil (Cons lo hi t0)) /\
(forall x : Z,
 (IntvSets.In x Nil \/ IntvSets.In x (Cons lo hi t0) -> IntvSets.In x (union Nil (Cons lo hi t0))) /\
 (IntvSets.In x (union Nil (Cons lo hi t0)) -> IntvSets.In x Nil \/ IntvSets.In x (Cons lo hi t0)))

).

  MetaCoq Quote Definition In_ok_union_Cons_Nil := (
    forall (lo hi : Z) (s1 : t),
(ok' s1 ->
 forall s2 : t,
 ok' s2 ->
 ok' (union s1 s2) /\
 (forall x : Z,
  (IntvSets.In x s1 \/ IntvSets.In x s2 -> IntvSets.In x (union s1 s2)) /\
  (IntvSets.In x (union s1 s2) -> IntvSets.In x s1 \/ IntvSets.In x s2))) ->
ok' (Cons lo hi s1) ->
forall s2 : t,
s2 = Nil ->
(forall s : t, ok' s -> forall l0 h0 : Z, l0 < h0 -> ok' (add l0 h0 s)) ->
(forall (x l0 h0 : Z) (s : t),
 ok' s ->
 (IntvSets.In x (IntvSets.remove l0 h0 s) -> ~ l0 <= x < h0 /\ IntvSets.In x s) /\
 (~ l0 <= x < h0 /\ IntvSets.In x s -> IntvSets.In x (IntvSets.remove l0 h0 s))) ->
(forall (x : Z) (s : t),
 ok' s ->
 forall l0 h0 : Z,
 (IntvSets.In x (add l0 h0 s) -> l0 <= x < h0 \/ IntvSets.In x s) /\
 (l0 <= x < h0 \/ IntvSets.In x s -> IntvSets.In x (add l0 h0 s))) ->
(forall (x l h : Z) (t : t),
 (l <= x < h \/ IntvSets.In x t -> IntvSets.In x (Cons l h t)) /\
 (IntvSets.In x (Cons l h t) -> l <= x < h \/ IntvSets.In x t)) ->
(forall z : Z, ~ IntvSets.In z Nil) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t)) ->
ok' Nil ->
(forall (x l h : Z) (t : t), mem x (Cons l h t) = ite (x <? h) (l <=? x) (mem x t)) ->
(forall x : Z, mem x Nil = false) ->
(forall (L H l h : Z) (t : t), contains L H (Cons l h t) = (H <=? h) && (l <=? L) || contains L H t) ->
(forall x y : Z, contains x y Nil = false) ->
(forall (L H l h : Z) (s' : t),
 add L H (Cons l h s') =
 ite (h <? L) (Cons l h (add L H s')) (ite (H <? l) (Cons L H (Cons l h s')) (add (Z.min l L) (Z.max h H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l h : Z) (s' : t),
 IntvSets.remove L H (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H s'))
   (ite (H <? l) (Cons l h s')
      (ite (l <? L) (ite (H <? h) (Cons l L (Cons H h s')) (Cons l L (IntvSets.remove L H s')))
         (ite (H <? h) (Cons H h s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t),
 union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s3 : t, union s3 Nil = s3) ->
(forall s3 : t, union Nil s3 = s3) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s : t), beq (Cons L H s) Nil = false) ->
(forall (L H : Z) (s : t), beq Nil (Cons L H s) = false) ->
beq Nil Nil = true ->
(forall x y : Z, Z.min x y = ite (x <? y) x y) ->
(forall x y : Z, Z.max x y = ite (x <? y) y x) ->
ok' Nil ->
ok' (union (Cons lo hi s1) Nil) /\
(forall x : Z,
 (IntvSets.In x (Cons lo hi s1) \/ IntvSets.In x Nil -> IntvSets.In x (union (Cons lo hi s1) Nil)) /\
 (IntvSets.In x (union (Cons lo hi s1) Nil) -> IntvSets.In x (Cons lo hi s1) \/ IntvSets.In x Nil))
  ).

MetaCoq Quote Definition In_ok_union_Cons_Cons := (
  forall (lo hi : Z) (s1 : t),
(ok' s1 ->
 forall s2 : t,
 ok' s2 ->
 ok' (union s1 s2) /\
 (forall x : Z,
  (IntvSets.In x s1 \/ IntvSets.In x s2 -> IntvSets.In x (union s1 s2)) /\
  (IntvSets.In x (union s1 s2) -> IntvSets.In x s1 \/ IntvSets.In x s2))) ->
ok' (Cons lo hi s1) ->
forall (s2 : t) (lo0 hi0 : Z) (t0 : t),
s2 = Cons lo0 hi0 t0 ->
(forall s : t, ok' s -> forall l0 h0 : Z, l0 < h0 -> ok' (add l0 h0 s)) ->
(forall (x l0 h0 : Z) (s : t),
 ok' s ->
 (IntvSets.In x (IntvSets.remove l0 h0 s) -> ~ l0 <= x < h0 /\ IntvSets.In x s) /\
 (~ l0 <= x < h0 /\ IntvSets.In x s -> IntvSets.In x (IntvSets.remove l0 h0 s))) ->
(forall (x : Z) (s : t),
 ok' s ->
 forall l0 h0 : Z,
 (IntvSets.In x (add l0 h0 s) -> l0 <= x < h0 \/ IntvSets.In x s) /\
 (l0 <= x < h0 \/ IntvSets.In x s -> IntvSets.In x (add l0 h0 s))) ->
(forall (x l h : Z) (t : t),
 (l <= x < h \/ IntvSets.In x t -> IntvSets.In x (Cons l h t)) /\
 (IntvSets.In x (Cons l h t) -> l <= x < h \/ IntvSets.In x t)) ->
(forall z : Z, ~ IntvSets.In z Nil) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t)) ->
ok' Nil ->
(forall (x l h : Z) (t : t), mem x (Cons l h t) = ite (x <? h) (l <=? x) (mem x t)) ->
(forall x : Z, mem x Nil = false) ->
(forall (L H l h : Z) (t : t), contains L H (Cons l h t) = (H <=? h) && (l <=? L) || contains L H t) ->
(forall x y : Z, contains x y Nil = false) ->
(forall (L H l h : Z) (s' : t),
 add L H (Cons l h s') =
 ite (h <? L) (Cons l h (add L H s')) (ite (H <? l) (Cons L H (Cons l h s')) (add (Z.min l L) (Z.max h H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l h : Z) (s' : t),
 IntvSets.remove L H (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H s'))
   (ite (H <? l) (Cons l h s')
      (ite (l <? L) (ite (H <? h) (Cons l L (Cons H h s')) (Cons l L (IntvSets.remove L H s')))
         (ite (H <? h) (Cons H h s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t),
 union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s3 : t, union s3 Nil = s3) ->
(forall s3 : t, union Nil s3 = s3) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s : t), beq (Cons L H s) Nil = false) ->
(forall (L H : Z) (s : t), beq Nil (Cons L H s) = false) ->
beq Nil Nil = true ->
(forall x y : Z, Z.min x y = ite (x <? y) x y) ->
(forall x y : Z, Z.max x y = ite (x <? y) y x) ->
ok' (Cons lo0 hi0 t0) ->
ok' (union (Cons lo hi s1) (Cons lo0 hi0 t0)) /\
(forall x : Z,
 (IntvSets.In x (Cons lo hi s1) \/ IntvSets.In x (Cons lo0 hi0 t0) ->
  IntvSets.In x (union (Cons lo hi s1) (Cons lo0 hi0 t0))) /\
 (IntvSets.In x (union (Cons lo hi s1) (Cons lo0 hi0 t0)) ->
  IntvSets.In x (Cons lo hi s1) \/ IntvSets.In x (Cons lo0 hi0 t0)))
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(*** MS BEGIN {"type": "configuration", "config_type":"plugin"} *)
SetSMTSolver "cvc5".
(*** MS END {"type": "configuration", "config_type":"plugin"} *)

(*** MS BEGIN {"type": "proof_definition"} *)
Lemma In_ok_union:
  forall s1, 
    ok s1 -> 
    forall s2, 
      ok s2 ->
      ok (union s1 s2) /\ 
      (forall x, IntvSets.In x s1 \/ IntvSets.In x s2 <-> IntvSets.In x (union s1 s2)).
(*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  induction 1; 
  destruct 1; 
  simpl.
  split.
  constructor.
  tauto.
  split.
  constructor;
  auto.
  tauto.
  split.
  constructor;
  auto.
  tauto.
  destruct (IHok s0) as [A B];
  auto.
  split.
  apply add_ok;
  auto.
  apply add_ok;
  auto.
  intros.
  rewrite In_add.
  rewrite In_add.
  rewrite <- B.
  tauto. 
  auto.
  apply add_ok;
  auto.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  intros.
  erewrite ok_ok' in *.
  Utils.revert_all.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":4, "finished":3} *)
  induction s1;
  destruct s2 eqn:?.
  - hammer.
  - hammer.
  - hammer.
  - admit. (* hammer. *)
  Restart.
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":4, "finished":3} *)
Proof.
  intros;
  erewrite ok_ok' in *;
  Utils.revert_all.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":4} *)
  induction s1;
  destruct s2 eqn:?;
  prep_proof'''.
  - reflect In_ok_union_Nil_Nil;
    check_goal_unsat.
  - reflect In_ok_union_Nil_Cons;
    check_goal_unsat.
  - reflect In_ok_union_Cons_Nil;
    check_goal_unsat.
  - reflect In_ok_union_Cons_Cons;
    check_goal_unsat.
(*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":4} *)
Qed.


(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition beq_spec_Nil_Nil := (
  
  ok' Nil ->
  forall s2 : t,
  s2 = Nil ->
  (forall s : t, ok' s -> forall l0 h0 : Z, l0 < h0 -> ok' (add l0 h0 s)) ->
  (forall (x l0 h0 : Z) (s : t),
   ok' s ->
   (IntvSets.In x (IntvSets.remove l0 h0 s) -> ~ l0 <= x < h0 /\ IntvSets.In x s) /\
   (~ l0 <= x < h0 /\ IntvSets.In x s -> IntvSets.In x (IntvSets.remove l0 h0 s))) ->
  (forall (x : Z) (s : t),
   ok' s ->
   forall l0 h0 : Z,
   (IntvSets.In x (add l0 h0 s) -> l0 <= x < h0 \/ IntvSets.In x s) /\
   (l0 <= x < h0 \/ IntvSets.In x s -> IntvSets.In x (add l0 h0 s))) ->
  (forall (x l h : Z) (t : t),
   (l <= x < h \/ IntvSets.In x t -> IntvSets.In x (Cons l h t)) /\
   (IntvSets.In x (Cons l h t) -> l <= x < h \/ IntvSets.In x t)) ->
  (forall z : Z, ~ IntvSets.In z Nil) ->
  (forall (l h : Z) (t : t),
   (l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t -> ok' (Cons l h t)) /\
   (ok' (Cons l h t) -> l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t)) ->
  ok' Nil ->
  (forall (x l h : Z) (t : t), mem x (Cons l h t) = ite (x <? h) (l <=? x) (mem x t)) ->
  (forall x : Z, mem x Nil = false) ->
  (forall (L H l h : Z) (t : t), contains L H (Cons l h t) = (H <=? h) && (l <=? L) || contains L H t) ->
  (forall x y : Z, contains x y Nil = false) ->
  (forall (L H l h : Z) (s' : t),
   add L H (Cons l h s') =
   ite (h <? L) (Cons l h (add L H s')) (ite (H <? l) (Cons L H (Cons l h s')) (add (Z.min l L) (Z.max h H) s'))) ->
  (forall L H : Z, add L H Nil = Cons L H Nil) ->
  (forall (L H l h : Z) (s' : t),
   IntvSets.remove L H (Cons l h s') =
   ite (h <? L) (Cons l h (IntvSets.remove L H s'))
     (ite (H <? l) (Cons l h s')
        (ite (l <? L) (ite (H <? h) (Cons l L (Cons H h s')) (Cons l L (IntvSets.remove L H s')))
           (ite (H <? h) (Cons H h s') (IntvSets.remove L H s'))))) ->
  (forall L H : Z, IntvSets.remove L H Nil = Nil) ->
  (forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
  (forall s1 : t, union s1 Nil = s1) ->
  (forall s3 : t, union Nil s3 = s3) ->
  (forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
   beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
  (forall (L H : Z) (s : t), beq (Cons L H s) Nil = false) ->
  (forall (L H : Z) (s : t), beq Nil (Cons L H s) = false) ->
  beq Nil Nil = true ->
  (forall x y : Z, Z.min x y = ite (x <? y) x y) ->
  (forall x y : Z, Z.max x y = ite (x <? y) y x) ->
  ok' Nil ->
  (beq Nil Nil = true -> forall x : Z, (IntvSets.In x Nil -> IntvSets.In x Nil) /\ (IntvSets.In x Nil -> IntvSets.In x Nil)) /\
  ((forall x : Z, (IntvSets.In x Nil -> IntvSets.In x Nil) /\ (IntvSets.In x Nil -> IntvSets.In x Nil)) ->
   beq Nil Nil = true)
).

MetaCoq Quote Definition beq_spec_Nil_Cons := (
  ok' Nil ->
forall (s2 : t) (lo hi : Z) (t0 : t),
s2 = Cons lo hi t0 ->
(forall s : t, ok' s -> forall l0 h0 : Z, l0 < h0 -> ok' (add l0 h0 s)) ->
(forall (x l0 h0 : Z) (s : t),
 ok' s ->
 (IntvSets.In x (IntvSets.remove l0 h0 s) -> ~ l0 <= x < h0 /\ IntvSets.In x s) /\
 (~ l0 <= x < h0 /\ IntvSets.In x s -> IntvSets.In x (IntvSets.remove l0 h0 s))) ->
(forall (x : Z) (s : t),
 ok' s ->
 forall l0 h0 : Z,
 (IntvSets.In x (add l0 h0 s) -> l0 <= x < h0 \/ IntvSets.In x s) /\
 (l0 <= x < h0 \/ IntvSets.In x s -> IntvSets.In x (add l0 h0 s))) ->
(forall (x l h : Z) (t : t),
 (l <= x < h \/ IntvSets.In x t -> IntvSets.In x (Cons l h t)) /\
 (IntvSets.In x (Cons l h t) -> l <= x < h \/ IntvSets.In x t)) ->
(forall z : Z, ~ IntvSets.In z Nil) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t)) ->
ok' Nil ->
(forall (x l h : Z) (t : t), mem x (Cons l h t) = ite (x <? h) (l <=? x) (mem x t)) ->
(forall x : Z, mem x Nil = false) ->
(forall (L H l h : Z) (t : t), contains L H (Cons l h t) = (H <=? h) && (l <=? L) || contains L H t) ->
(forall x y : Z, contains x y Nil = false) ->
(forall (L H l h : Z) (s' : t),
 add L H (Cons l h s') =
 ite (h <? L) (Cons l h (add L H s')) (ite (H <? l) (Cons L H (Cons l h s')) (add (Z.min l L) (Z.max h H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l h : Z) (s' : t),
 IntvSets.remove L H (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H s'))
   (ite (H <? l) (Cons l h s')
      (ite (l <? L) (ite (H <? h) (Cons l L (Cons H h s')) (Cons l L (IntvSets.remove L H s')))
         (ite (H <? h) (Cons H h s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s1 : t, union s1 Nil = s1) ->
(forall s3 : t, union Nil s3 = s3) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s : t), beq (Cons L H s) Nil = false) ->
(forall (L H : Z) (s : t), beq Nil (Cons L H s) = false) ->
beq Nil Nil = true ->
(forall x y : Z, Z.min x y = ite (x <? y) x y) ->
(forall x y : Z, Z.max x y = ite (x <? y) y x) ->
ok' (Cons lo hi t0) ->
(beq Nil (Cons lo hi t0) = true ->
 forall x : Z,
 (IntvSets.In x Nil -> IntvSets.In x (Cons lo hi t0)) /\ (IntvSets.In x (Cons lo hi t0) -> IntvSets.In x Nil)) /\
((forall x : Z,
  (IntvSets.In x Nil -> IntvSets.In x (Cons lo hi t0)) /\ (IntvSets.In x (Cons lo hi t0) -> IntvSets.In x Nil)) ->
 beq Nil (Cons lo hi t0) = true)
).

  MetaCoq Quote Definition beq_spec_Cons_Nil := (
    forall (lo hi : Z) (s1 : t),
(ok' s1 ->
 forall s2 : t,
 ok' s2 ->
 (beq s1 s2 = true -> forall x : Z, (IntvSets.In x s1 -> IntvSets.In x s2) /\ (IntvSets.In x s2 -> IntvSets.In x s1)) /\
 ((forall x : Z, (IntvSets.In x s1 -> IntvSets.In x s2) /\ (IntvSets.In x s2 -> IntvSets.In x s1)) -> beq s1 s2 = true)) ->
ok' (Cons lo hi s1) ->
forall s2 : t,
s2 = Nil ->
(forall s : t, ok' s -> forall l0 h0 : Z, l0 < h0 -> ok' (add l0 h0 s)) ->
(forall (x l0 h0 : Z) (s : t),
 ok' s ->
 (IntvSets.In x (IntvSets.remove l0 h0 s) -> ~ l0 <= x < h0 /\ IntvSets.In x s) /\
 (~ l0 <= x < h0 /\ IntvSets.In x s -> IntvSets.In x (IntvSets.remove l0 h0 s))) ->
(forall (x : Z) (s : t),
 ok' s ->
 forall l0 h0 : Z,
 (IntvSets.In x (add l0 h0 s) -> l0 <= x < h0 \/ IntvSets.In x s) /\
 (l0 <= x < h0 \/ IntvSets.In x s -> IntvSets.In x (add l0 h0 s))) ->
(forall (x l h : Z) (t : t),
 (l <= x < h \/ IntvSets.In x t -> IntvSets.In x (Cons l h t)) /\
 (IntvSets.In x (Cons l h t) -> l <= x < h \/ IntvSets.In x t)) ->
(forall z : Z, ~ IntvSets.In z Nil) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t)) ->
ok' Nil ->
(forall (x l h : Z) (t : t), mem x (Cons l h t) = ite (x <? h) (l <=? x) (mem x t)) ->
(forall x : Z, mem x Nil = false) ->
(forall (L H l h : Z) (t : t), contains L H (Cons l h t) = (H <=? h) && (l <=? L) || contains L H t) ->
(forall x y : Z, contains x y Nil = false) ->
(forall (L H l h : Z) (s' : t),
 add L H (Cons l h s') =
 ite (h <? L) (Cons l h (add L H s')) (ite (H <? l) (Cons L H (Cons l h s')) (add (Z.min l L) (Z.max h H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l h : Z) (s' : t),
 IntvSets.remove L H (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H s'))
   (ite (H <? l) (Cons l h s')
      (ite (l <? L) (ite (H <? h) (Cons l L (Cons H h s')) (Cons l L (IntvSets.remove L H s')))
         (ite (H <? h) (Cons H h s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s3 : t, union s3 Nil = s3) ->
(forall s3 : t, union Nil s3 = s3) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s : t), beq (Cons L H s) Nil = false) ->
(forall (L H : Z) (s : t), beq Nil (Cons L H s) = false) ->
beq Nil Nil = true ->
(forall x y : Z, Z.min x y = ite (x <? y) x y) ->
(forall x y : Z, Z.max x y = ite (x <? y) y x) ->
ok' Nil ->
(beq (Cons lo hi s1) Nil = true ->
 forall x : Z,
 (IntvSets.In x (Cons lo hi s1) -> IntvSets.In x Nil) /\ (IntvSets.In x Nil -> IntvSets.In x (Cons lo hi s1))) /\
((forall x : Z,
  (IntvSets.In x (Cons lo hi s1) -> IntvSets.In x Nil) /\ (IntvSets.In x Nil -> IntvSets.In x (Cons lo hi s1))) ->
 beq (Cons lo hi s1) Nil = true)
  ).

MetaCoq Quote Definition beq_spec_Cons_Cons_0 := (
  forall (lo hi : Z) (s1 : t),
  (ok' s1 ->
   forall s2 : t,
   ok' s2 ->
   (beq s1 s2 = true -> forall x : Z, (IntvSets.In x s1 -> IntvSets.In x s2) /\ (IntvSets.In x s2 -> IntvSets.In x s1)) /\
   ((forall x : Z, (IntvSets.In x s1 -> IntvSets.In x s2) /\ (IntvSets.In x s2 -> IntvSets.In x s1)) -> beq s1 s2 = true)) ->
  lo < hi /\ (forall x : Z, IntvSets.In x s1 -> hi < x) /\ ok' s1 ->
  forall (s2 : t) (lo0 hi0 : Z) (t0 : t),
  s2 = Cons lo0 hi0 t0 ->
  lo0 < hi0 /\ (forall x : Z, IntvSets.In x t0 -> hi0 < x) /\ ok' t0 ->
  (lo =? lo0) && (hi =? hi0) && beq s1 t0 = true ->
  forall x : Z,
  (forall s : t, ok' s -> forall l0 h0 : Z, l0 < h0 -> ok' (add l0 h0 s)) ->
  (forall (x0 l0 h0 : Z) (s : t),
   ok' s ->
   (IntvSets.In x0 (IntvSets.remove l0 h0 s) -> ~ l0 <= x0 < h0 /\ IntvSets.In x0 s) /\
   (~ l0 <= x0 < h0 /\ IntvSets.In x0 s -> IntvSets.In x0 (IntvSets.remove l0 h0 s))) ->
  (forall (x0 : Z) (s : t),
   ok' s ->
   forall l0 h0 : Z,
   (IntvSets.In x0 (add l0 h0 s) -> l0 <= x0 < h0 \/ IntvSets.In x0 s) /\
   (l0 <= x0 < h0 \/ IntvSets.In x0 s -> IntvSets.In x0 (add l0 h0 s))) ->
  (forall (x0 l h : Z) (t : t),
   (l <= x0 < h \/ IntvSets.In x0 t -> IntvSets.In x0 (Cons l h t)) /\
   (IntvSets.In x0 (Cons l h t) -> l <= x0 < h \/ IntvSets.In x0 t)) ->
  (forall z : Z, ~ IntvSets.In z Nil) ->
  (forall (l h : Z) (t : t),
   (l < h /\ (forall x0 : Z, IntvSets.In x0 t -> h < x0) /\ ok' t -> ok' (Cons l h t)) /\
   (ok' (Cons l h t) -> l < h /\ (forall x0 : Z, IntvSets.In x0 t -> h < x0) /\ ok' t)) ->
  ok' Nil ->
  (forall (x0 l h : Z) (t : t), mem x0 (Cons l h t) = ite (x0 <? h) (l <=? x0) (mem x0 t)) ->
  (forall x0 : Z, mem x0 Nil = false) ->
  (forall (L H l h : Z) (t : t), contains L H (Cons l h t) = (H <=? h) && (l <=? L) || contains L H t) ->
  (forall x0 y : Z, contains x0 y Nil = false) ->
  (forall (L H l h : Z) (s' : t),
   add L H (Cons l h s') =
   ite (h <? L) (Cons l h (add L H s')) (ite (H <? l) (Cons L H (Cons l h s')) (add (Z.min l L) (Z.max h H) s'))) ->
  (forall L H : Z, add L H Nil = Cons L H Nil) ->
  (forall (L H l h : Z) (s' : t),
   IntvSets.remove L H (Cons l h s') =
   ite (h <? L) (Cons l h (IntvSets.remove L H s'))
     (ite (H <? l) (Cons l h s')
        (ite (l <? L) (ite (H <? h) (Cons l L (Cons H h s')) (Cons l L (IntvSets.remove L H s')))
           (ite (H <? h) (Cons H h s') (IntvSets.remove L H s'))))) ->
  (forall L H : Z, IntvSets.remove L H Nil = Nil) ->
  (forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
  (forall s3 : t, union s3 Nil = s3) ->
  (forall s3 : t, union Nil s3 = s3) ->
  (forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
   beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
  (forall (L H : Z) (s : t), beq (Cons L H s) Nil = false) ->
  (forall (L H : Z) (s : t), beq Nil (Cons L H s) = false) ->
  beq Nil Nil = true ->
  (forall x0 y : Z, Z.min x0 y = ite (x0 <? y) x0 y) ->
  (forall x0 y : Z, Z.max x0 y = ite (x0 <? y) y x0) ->
  (lo <= x < hi \/ IntvSets.In x s1 -> lo0 <= x < hi0 \/ IntvSets.In x t0) /\
  (lo0 <= x < hi0 \/ IntvSets.In x t0 -> lo <= x < hi \/ IntvSets.In x s1)
).


MetaCoq Quote Definition beq_spec_Cons_Cons_11 := (
  
forall (lo hi : Z) (s1 : t),
(ok' s1 ->
 forall s2 : t,
 ok' s2 ->
 (beq s1 s2 = true -> forall x : Z, (IntvSets.In x s1 -> IntvSets.In x s2) /\ (IntvSets.In x s2 -> IntvSets.In x s1)) /\
 ((forall x : Z, (IntvSets.In x s1 -> IntvSets.In x s2) /\ (IntvSets.In x s2 -> IntvSets.In x s1)) -> beq s1 s2 = true)) ->
lo < hi /\ (forall x : Z, IntvSets.In x s1 -> hi < x) /\ ok' s1 ->
forall (s2 : t) (lo0 hi0 : Z) (t0 : t),
s2 = Cons lo0 hi0 t0 ->
lo0 < hi0 /\ (forall x : Z, IntvSets.In x t0 -> hi0 < x) /\ ok' t0 ->
(forall x : Z,
 (lo <= x < hi \/ IntvSets.In x s1 -> lo0 <= x < hi0 \/ IntvSets.In x t0) /\
 (lo0 <= x < hi0 \/ IntvSets.In x t0 -> lo <= x < hi \/ IntvSets.In x s1)) ->
(lo =? lo0) = true ->
(hi =? hi0) = true ->
(forall s : t, ok' s -> forall l0 h0 : Z, l0 < h0 -> ok' (add l0 h0 s)) ->
(forall (x l0 h0 : Z) (s : t),
 ok' s ->
 (IntvSets.In x (IntvSets.remove l0 h0 s) -> ~ l0 <= x < h0 /\ IntvSets.In x s) /\
 (~ l0 <= x < h0 /\ IntvSets.In x s -> IntvSets.In x (IntvSets.remove l0 h0 s))) ->
(forall (x : Z) (s : t),
 ok' s ->
 forall l0 h0 : Z,
 (IntvSets.In x (add l0 h0 s) -> l0 <= x < h0 \/ IntvSets.In x s) /\
 (l0 <= x < h0 \/ IntvSets.In x s -> IntvSets.In x (add l0 h0 s))) ->
(forall (x l h : Z) (t : t),
 (l <= x < h \/ IntvSets.In x t -> IntvSets.In x (Cons l h t)) /\
 (IntvSets.In x (Cons l h t) -> l <= x < h \/ IntvSets.In x t)) ->
(forall z : Z, ~ IntvSets.In z Nil) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t)) ->
ok' Nil ->
(forall (x l h : Z) (t : t), mem x (Cons l h t) = ite (x <? h) (l <=? x) (mem x t)) ->
(forall x : Z, mem x Nil = false) ->
(forall (L H l h : Z) (t : t), contains L H (Cons l h t) = (H <=? h) && (l <=? L) || contains L H t) ->
(forall x y : Z, contains x y Nil = false) ->
(forall (L H l h : Z) (s' : t),
 add L H (Cons l h s') =
 ite (h <? L) (Cons l h (add L H s')) (ite (H <? l) (Cons L H (Cons l h s')) (add (Z.min l L) (Z.max h H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l h : Z) (s' : t),
 IntvSets.remove L H (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H s'))
   (ite (H <? l) (Cons l h s')
      (ite (l <? L) (ite (H <? h) (Cons l L (Cons H h s')) (Cons l L (IntvSets.remove L H s')))
         (ite (H <? h) (Cons H h s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s3 : t, union s3 Nil = s3) ->
(forall s3 : t, union Nil s3 = s3) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s : t), beq (Cons L H s) Nil = false) ->
(forall (L H : Z) (s : t), beq Nil (Cons L H s) = false) ->
beq Nil Nil = true ->
(forall x y : Z, Z.min x y = ite (x <? y) x y) -> (forall x y : Z, Z.max x y = ite (x <? y) y x) -> ok' s1

).

MetaCoq Quote Definition beq_spec_Cons_Cons_12 := (
  
forall (lo hi : Z) (s1 : t),
(ok' s1 ->
 forall s2 : t,
 ok' s2 ->
 (beq s1 s2 = true -> forall x : Z, (IntvSets.In x s1 -> IntvSets.In x s2) /\ (IntvSets.In x s2 -> IntvSets.In x s1)) /\
 ((forall x : Z, (IntvSets.In x s1 -> IntvSets.In x s2) /\ (IntvSets.In x s2 -> IntvSets.In x s1)) -> beq s1 s2 = true)) ->
lo < hi /\ (forall x : Z, IntvSets.In x s1 -> hi < x) /\ ok' s1 ->
forall (s2 : t) (lo0 hi0 : Z) (t0 : t),
s2 = Cons lo0 hi0 t0 ->
lo0 < hi0 /\ (forall x : Z, IntvSets.In x t0 -> hi0 < x) /\ ok' t0 ->
(forall x : Z,
 (lo <= x < hi \/ IntvSets.In x s1 -> lo0 <= x < hi0 \/ IntvSets.In x t0) /\
 (lo0 <= x < hi0 \/ IntvSets.In x t0 -> lo <= x < hi \/ IntvSets.In x s1)) ->
(lo =? lo0) = true ->
(hi =? hi0) = true ->
(forall s : t, ok' s -> forall l0 h0 : Z, l0 < h0 -> ok' (add l0 h0 s)) ->
(forall (x l0 h0 : Z) (s : t),
 ok' s ->
 (IntvSets.In x (IntvSets.remove l0 h0 s) -> ~ l0 <= x < h0 /\ IntvSets.In x s) /\
 (~ l0 <= x < h0 /\ IntvSets.In x s -> IntvSets.In x (IntvSets.remove l0 h0 s))) ->
(forall (x : Z) (s : t),
 ok' s ->
 forall l0 h0 : Z,
 (IntvSets.In x (add l0 h0 s) -> l0 <= x < h0 \/ IntvSets.In x s) /\
 (l0 <= x < h0 \/ IntvSets.In x s -> IntvSets.In x (add l0 h0 s))) ->
(forall (x l h : Z) (t : t),
 (l <= x < h \/ IntvSets.In x t -> IntvSets.In x (Cons l h t)) /\
 (IntvSets.In x (Cons l h t) -> l <= x < h \/ IntvSets.In x t)) ->
(forall z : Z, ~ IntvSets.In z Nil) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t)) ->
ok' Nil ->
(forall (x l h : Z) (t : t), mem x (Cons l h t) = ite (x <? h) (l <=? x) (mem x t)) ->
(forall x : Z, mem x Nil = false) ->
(forall (L H l h : Z) (t : t), contains L H (Cons l h t) = (H <=? h) && (l <=? L) || contains L H t) ->
(forall x y : Z, contains x y Nil = false) ->
(forall (L H l h : Z) (s' : t),
 add L H (Cons l h s') =
 ite (h <? L) (Cons l h (add L H s')) (ite (H <? l) (Cons L H (Cons l h s')) (add (Z.min l L) (Z.max h H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l h : Z) (s' : t),
 IntvSets.remove L H (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H s'))
   (ite (H <? l) (Cons l h s')
      (ite (l <? L) (ite (H <? h) (Cons l L (Cons H h s')) (Cons l L (IntvSets.remove L H s')))
         (ite (H <? h) (Cons H h s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s3 : t, union s3 Nil = s3) ->
(forall s3 : t, union Nil s3 = s3) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s : t), beq (Cons L H s) Nil = false) ->
(forall (L H : Z) (s : t), beq Nil (Cons L H s) = false) ->
beq Nil Nil = true ->
(forall x y : Z, Z.min x y = ite (x <? y) x y) -> (forall x y : Z, Z.max x y = ite (x <? y) y x) -> ok' t0

).

MetaCoq Quote Definition beq_spec_Cons_Cons_13 := (
  forall (lo hi : Z) (s1 : t),
(ok' s1 ->
 forall s2 : t,
 ok' s2 ->
 (beq s1 s2 = true -> forall x : Z, (IntvSets.In x s1 -> IntvSets.In x s2) /\ (IntvSets.In x s2 -> IntvSets.In x s1)) /\
 ((forall x : Z, (IntvSets.In x s1 -> IntvSets.In x s2) /\ (IntvSets.In x s2 -> IntvSets.In x s1)) -> beq s1 s2 = true)) ->
lo < hi /\ (forall x : Z, IntvSets.In x s1 -> hi < x) /\ ok' s1 ->
forall (s2 : t) (lo0 hi0 : Z) (t0 : t),
s2 = Cons lo0 hi0 t0 ->
lo0 < hi0 /\ (forall x : Z, IntvSets.In x t0 -> hi0 < x) /\ ok' t0 ->
(forall x : Z,
 (lo <= x < hi \/ IntvSets.In x s1 -> lo0 <= x < hi0 \/ IntvSets.In x t0) /\
 (lo0 <= x < hi0 \/ IntvSets.In x t0 -> lo <= x < hi \/ IntvSets.In x s1)) ->
(lo =? lo0) = true ->
(hi =? hi0) = true ->
(forall s : t, ok' s -> forall l0 h0 : Z, l0 < h0 -> ok' (add l0 h0 s)) ->
(forall (x l0 h0 : Z) (s : t),
 ok' s ->
 (IntvSets.In x (IntvSets.remove l0 h0 s) -> ~ l0 <= x < h0 /\ IntvSets.In x s) /\
 (~ l0 <= x < h0 /\ IntvSets.In x s -> IntvSets.In x (IntvSets.remove l0 h0 s))) ->
(forall (x : Z) (s : t),
 ok' s ->
 forall l0 h0 : Z,
 (IntvSets.In x (add l0 h0 s) -> l0 <= x < h0 \/ IntvSets.In x s) /\
 (l0 <= x < h0 \/ IntvSets.In x s -> IntvSets.In x (add l0 h0 s))) ->
(forall (x l h : Z) (t : t),
 (l <= x < h \/ IntvSets.In x t -> IntvSets.In x (Cons l h t)) /\
 (IntvSets.In x (Cons l h t) -> l <= x < h \/ IntvSets.In x t)) ->
(forall z : Z, ~ IntvSets.In z Nil) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t)) ->
ok' Nil ->
(forall (x l h : Z) (t : t), mem x (Cons l h t) = ite (x <? h) (l <=? x) (mem x t)) ->
(forall x : Z, mem x Nil = false) ->
(forall (L H l h : Z) (t : t), contains L H (Cons l h t) = (H <=? h) && (l <=? L) || contains L H t) ->
(forall x y : Z, contains x y Nil = false) ->
(forall (L H l h : Z) (s' : t),
 add L H (Cons l h s') =
 ite (h <? L) (Cons l h (add L H s')) (ite (H <? l) (Cons L H (Cons l h s')) (add (Z.min l L) (Z.max h H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l h : Z) (s' : t),
 IntvSets.remove L H (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H s'))
   (ite (H <? l) (Cons l h s')
      (ite (l <? L) (ite (H <? h) (Cons l L (Cons H h s')) (Cons l L (IntvSets.remove L H s')))
         (ite (H <? h) (Cons H h s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s3 : t, union s3 Nil = s3) ->
(forall s3 : t, union Nil s3 = s3) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s : t), beq (Cons L H s) Nil = false) ->
(forall (L H : Z) (s : t), beq Nil (Cons L H s) = false) ->
beq Nil Nil = true ->
(forall x y : Z, Z.min x y = ite (x <? y) x y) ->
(forall x y : Z, Z.max x y = ite (x <? y) y x) ->
forall x : Z, (IntvSets.In x s1 -> IntvSets.In x t0) /\ (IntvSets.In x t0 -> IntvSets.In x s1)


).

MetaCoq Quote Definition beq_spec_Cons_Cons_14 := (
  forall (lo hi : Z) (s1 : t),
(ok' s1 ->
 forall s2 : t,
 ok' s2 ->
 (beq s1 s2 = true -> forall x : Z, (IntvSets.In x s1 -> IntvSets.In x s2) /\ (IntvSets.In x s2 -> IntvSets.In x s1)) /\
 ((forall x : Z, (IntvSets.In x s1 -> IntvSets.In x s2) /\ (IntvSets.In x s2 -> IntvSets.In x s1)) -> beq s1 s2 = true)) ->
lo < hi /\ (forall x : Z, IntvSets.In x s1 -> hi < x) /\ ok' s1 ->
forall (s2 : t) (lo0 hi0 : Z) (t0 : t),
s2 = Cons lo0 hi0 t0 ->
lo0 < hi0 /\ (forall x : Z, IntvSets.In x t0 -> hi0 < x) /\ ok' t0 ->
(forall x : Z,
 (lo <= x < hi \/ IntvSets.In x s1 -> lo0 <= x < hi0 \/ IntvSets.In x t0) /\
 (lo0 <= x < hi0 \/ IntvSets.In x t0 -> lo <= x < hi \/ IntvSets.In x s1)) ->
(lo =? lo0) = false ->
(forall s : t, ok' s -> forall l0 h0 : Z, l0 < h0 -> ok' (add l0 h0 s)) ->
(forall (x l0 h0 : Z) (s : t),
 ok' s ->
 (IntvSets.In x (IntvSets.remove l0 h0 s) -> ~ l0 <= x < h0 /\ IntvSets.In x s) /\
 (~ l0 <= x < h0 /\ IntvSets.In x s -> IntvSets.In x (IntvSets.remove l0 h0 s))) ->
(forall (x : Z) (s : t),
 ok' s ->
 forall l0 h0 : Z,
 (IntvSets.In x (add l0 h0 s) -> l0 <= x < h0 \/ IntvSets.In x s) /\
 (l0 <= x < h0 \/ IntvSets.In x s -> IntvSets.In x (add l0 h0 s))) ->
(forall (x l h : Z) (t : t),
 (l <= x < h \/ IntvSets.In x t -> IntvSets.In x (Cons l h t)) /\
 (IntvSets.In x (Cons l h t) -> l <= x < h \/ IntvSets.In x t)) ->
(forall z : Z, ~ IntvSets.In z Nil) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t)) ->
ok' Nil ->
(forall (x l h : Z) (t : t), mem x (Cons l h t) = ite (x <? h) (l <=? x) (mem x t)) ->
(forall x : Z, mem x Nil = false) ->
(forall (L H l h : Z) (t : t), contains L H (Cons l h t) = (H <=? h) && (l <=? L) || contains L H t) ->
(forall x y : Z, contains x y Nil = false) ->
(forall (L H l h : Z) (s' : t),
 add L H (Cons l h s') =
 ite (h <? L) (Cons l h (add L H s')) (ite (H <? l) (Cons L H (Cons l h s')) (add (Z.min l L) (Z.max h H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l h : Z) (s' : t),
 IntvSets.remove L H (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H s'))
   (ite (H <? l) (Cons l h s')
      (ite (l <? L) (ite (H <? h) (Cons l L (Cons H h s')) (Cons l L (IntvSets.remove L H s')))
         (ite (H <? h) (Cons H h s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s3 : t, union s3 Nil = s3) ->
(forall s3 : t, union Nil s3 = s3) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s : t), beq (Cons L H s) Nil = false) ->
(forall (L H : Z) (s : t), beq Nil (Cons L H s) = false) ->
beq Nil Nil = true ->
(forall x y : Z, Z.min x y = ite (x <? y) x y) ->
(forall x y : Z, Z.max x y = ite (x <? y) y x) -> false && (hi =? hi0) && beq s1 t0 = true
).

MetaCoq Quote Definition beq_spec_Cons_Cons_15 := (
  
forall (lo hi : Z) (s1 : t),
(ok' s1 ->
 forall s2 : t,
 ok' s2 ->
 (beq s1 s2 = true -> forall x : Z, (IntvSets.In x s1 -> IntvSets.In x s2) /\ (IntvSets.In x s2 -> IntvSets.In x s1)) /\
 ((forall x : Z, (IntvSets.In x s1 -> IntvSets.In x s2) /\ (IntvSets.In x s2 -> IntvSets.In x s1)) -> beq s1 s2 = true)) ->
lo < hi /\ (forall x : Z, IntvSets.In x s1 -> hi < x) /\ ok' s1 ->
forall (s2 : t) (lo0 hi0 : Z) (t0 : t),
s2 = Cons lo0 hi0 t0 ->
lo0 < hi0 /\ (forall x : Z, IntvSets.In x t0 -> hi0 < x) /\ ok' t0 ->
(forall x : Z,
 (lo <= x < hi \/ IntvSets.In x s1 -> lo0 <= x < hi0 \/ IntvSets.In x t0) /\
 (lo0 <= x < hi0 \/ IntvSets.In x t0 -> lo <= x < hi \/ IntvSets.In x s1)) ->
(lo =? lo0) = true ->
(hi =? hi0) = false ->
(forall s : t, ok' s -> forall l0 h0 : Z, l0 < h0 -> ok' (add l0 h0 s)) ->
(forall (x l0 h0 : Z) (s : t),
 ok' s ->
 (IntvSets.In x (IntvSets.remove l0 h0 s) -> ~ l0 <= x < h0 /\ IntvSets.In x s) /\
 (~ l0 <= x < h0 /\ IntvSets.In x s -> IntvSets.In x (IntvSets.remove l0 h0 s))) ->
(forall (x : Z) (s : t),
 ok' s ->
 forall l0 h0 : Z,
 (IntvSets.In x (add l0 h0 s) -> l0 <= x < h0 \/ IntvSets.In x s) /\
 (l0 <= x < h0 \/ IntvSets.In x s -> IntvSets.In x (add l0 h0 s))) ->
(forall (x l h : Z) (t : t),
 (l <= x < h \/ IntvSets.In x t -> IntvSets.In x (Cons l h t)) /\
 (IntvSets.In x (Cons l h t) -> l <= x < h \/ IntvSets.In x t)) ->
(forall z : Z, ~ IntvSets.In z Nil) ->
(forall (l h : Z) (t : t),
 (l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t -> ok' (Cons l h t)) /\
 (ok' (Cons l h t) -> l < h /\ (forall x : Z, IntvSets.In x t -> h < x) /\ ok' t)) ->
ok' Nil ->
(forall (x l h : Z) (t : t), mem x (Cons l h t) = ite (x <? h) (l <=? x) (mem x t)) ->
(forall x : Z, mem x Nil = false) ->
(forall (L H l h : Z) (t : t), contains L H (Cons l h t) = (H <=? h) && (l <=? L) || contains L H t) ->
(forall x y : Z, contains x y Nil = false) ->
(forall (L H l h : Z) (s' : t),
 add L H (Cons l h s') =
 ite (h <? L) (Cons l h (add L H s')) (ite (H <? l) (Cons L H (Cons l h s')) (add (Z.min l L) (Z.max h H) s'))) ->
(forall L H : Z, add L H Nil = Cons L H Nil) ->
(forall (L H l h : Z) (s' : t),
 IntvSets.remove L H (Cons l h s') =
 ite (h <? L) (Cons l h (IntvSets.remove L H s'))
   (ite (H <? l) (Cons l h s')
      (ite (l <? L) (ite (H <? h) (Cons l L (Cons H h s')) (Cons l L (IntvSets.remove L H s')))
         (ite (H <? h) (Cons H h s') (IntvSets.remove L H s'))))) ->
(forall L H : Z, IntvSets.remove L H Nil = Nil) ->
(forall (l1 l2 h1 h2 : Z) (s1' s2' : t), union (Cons l1 h1 s1') (Cons l2 h2 s2') = add l1 h1 (add l2 h2 (union s1' s2'))) ->
(forall s3 : t, union s3 Nil = s3) ->
(forall s3 : t, union Nil s3 = s3) ->
(forall (l1 h1 : Z) (t1 : t) (l2 h2 : Z) (t2 : t),
 beq (Cons l1 h1 t1) (Cons l2 h2 t2) = (l1 =? l2) && (h1 =? h2) && beq t1 t2) ->
(forall (L H : Z) (s : t), beq (Cons L H s) Nil = false) ->
(forall (L H : Z) (s : t), beq Nil (Cons L H s) = false) ->
beq Nil Nil = true ->
(forall x y : Z, Z.min x y = ite (x <? y) x y) ->
(forall x y : Z, Z.max x y = ite (x <? y) y x) -> true && false && beq s1 t0 = true
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(*** MS BEGIN {"type": "proof_definition"} *)
Lemma beq_spec:
  forall s1,  
    ok s1 -> 
    forall s2, 
      ok s2 ->
      (beq s1 s2 = true <-> (forall x, IntvSets.In x s1 <-> IntvSets.In x s2)).
(*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  induction 1; 
  destruct 1; 
  simpl.
- tauto.
- split;
  intros.
  discriminate.
  exfalso.
  apply (H0 l).
  left;
  lia.
- split;
  intros.
  discriminate.
  exfalso.
  apply (H0 l).
  left;
  lia.
- split; 
  intros.
  + InvBooleans. 
    subst. 
    rewrite IHok in H3 by auto.
    rewrite H3.
    intuition.
  + destruct (Z.eqb l l0) eqn:?;
    simpl.
    destruct (Z.eqb h h0) eqn:?;
    simpl.
    apply IHok.
    auto.
    intros;
    split;
    intros.
    destruct (proj1 (H1 x));
    auto.
    exfalso.
    exploit BELOW;
    eauto.
    lia.
    destruct (proj2 (H1 x));
    auto.
    exfalso.
    exploit BELOW0;
    eauto. 
    lia.
    exfalso. 
    destruct (zlt h h0).
    destruct (proj2 (H1 h)). 
    left; 
    lia. 
    lia. 
    exploit BELOW; 
    eauto. 
    lia.
    destruct (proj1 (H1 h0)). 
    left; 
    lia. 
    lia. 
    exploit BELOW0; 
    eauto. 
    lia.
    exfalso. 
    destruct (zlt l l0).
    destruct (proj1 (H1 l)).
    left;
    lia.
    lia.
    exploit BELOW0;
    eauto.
    lia.
    destruct (proj2 (H1 l0)).
    left;
    lia.
    lia.
    exploit BELOW;
    eauto.
    lia.
    (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
  Proof.
    intros.
    erewrite ok_ok' in *.
    Utils.revert_all.
    (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":4, "finished":2} *)
    induction s1;
    destruct s2 eqn:?.
    - hammer.
    - admit. (* hammer. *) (* succeeds *)
    - admit. (* hammer. *)
    - admit. (* hammer. *)
    Restart.
    (*** MS END {"type": "proof", "proof_type":"hammer", "total":4, "finished":2} *)
  Proof.
    intros;
    erewrite ok_ok' in *;
    Utils.revert_all.
    (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":4} *)
    induction s1;
    destruct s2 eqn:?.
    1-3: prep_proof'''.
    - reflect beq_spec_Nil_Nil;
      check_goal_unsat.
    - SetSMTSolver "z3".
      reflect beq_spec_Nil_Cons;
      check_goal_unsat.
    - reflect beq_spec_Cons_Nil;
      check_goal_unsat.
    - simpl in *.
      split;
      intros.
      prep_proof'''.
      + reflect beq_spec_Cons_Cons_0;
        check_goal_unsat.
      + destruct (lo =? lo0) eqn:?; [
          | shelve
        ];
        destruct (hi =? hi0) eqn:?; [
          | shelve
        ];
        simpl.
        eapply IHs1;
        eauto.
        Unshelve.
        1-3: prep_proof'''.
        -- reflect beq_spec_Cons_Cons_11;
           check_goal_unsat.
        -- reflect beq_spec_Cons_Cons_12;
           check_goal_unsat.
        -- reflect beq_spec_Cons_Cons_13;
           check_goal_unsat.
        -- admit.
        -- admit. (* TODO *)
  (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":4} *)
Admitted.

End ISet.





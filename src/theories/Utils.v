Require Import Coq.Setoids.Setoid.

Lemma some_ty: 
  forall {T} {x x': T},
    Some x = Some x' <-> 
    x = x'.
Proof.
  intros.
  intuition (inversion H; eauto).
Qed.

Lemma some_prop: 
  forall p p': Prop,
    Some p = Some p' <-> 
    p = p'.
Proof.
  intros.
  eapply some_ty.
Qed.

Lemma iff_distribute:
  forall a b c d : Prop,
    (a <-> c) -> 
    (b <-> d) -> 
    ((a -> b) <-> (c -> d)).
Proof.
  intros.
  erewrite H.
  erewrite H0.
  eapply iff_refl.
Qed.

Ltac revert_hyp H := 
  refine ((_ : _ -> _) H); clear H.

Ltac revert_hyps := 
  repeat match goal with
  | H: _ |- _ => revert_hyp H
  end.

Ltac revert_all := 
  repeat match goal with
  | H: _ |- _ => revert_hyp H || clear H || revert H
  end.

Ltac pose_all Pfs := 
  match Pfs with 
  | (?Pfs', ?Pf) => pose proof Pf; pose_all Pfs'
  | _ => idtac
  end.

Section SetList.
  Require Import Coq.Lists.List.
  Variable (V: Type).
  Variable (eqb: V -> V -> bool).

  Fixpoint inb (x: V) (xs: list V) : bool := 
    match xs with 
    | nil => false
    | x' :: xs' => 
      if eqb x x' then true else inb x xs'
    end.

  Fixpoint uniq (xs: list V) : list V := 
    match xs with 
    | nil => nil
    | x :: xs' => 
      let r := uniq xs' in 
      if inb x r then r else x :: r
    end.

End SetList.

Section AssocList.

  Require Import Coq.Lists.List.

  Variable (K V: Type).
  Variable (eqb: K -> K -> bool).

  Fixpoint find (k: K) (xs: list (K * V)) : option V := 
    match xs with 
    | (k', v) :: xs' => 
      if eqb k k' then Some v else find k xs'
    | nil => None
    end.
  
  Definition assoc (k : K) (v : V) xs := (k, v) :: xs.

End AssocList.

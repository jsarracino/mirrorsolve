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

Ltac revert_all := 
  repeat match goal with 
  | H : _ |- _ => 
    revert H
  end.

Ltac pose_all Pfs := 
  match Pfs with 
  | (?Pfs', ?Pf) => pose proof Pf; pose_all Pfs'
  | _ => idtac
  end.
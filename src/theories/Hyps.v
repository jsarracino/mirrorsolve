Record WithHyps : Type :=
  WrapHyps { hyps : list Prop ; p: Prop }.

Require Import Coq.Lists.List.

Import ListNotations.

Fixpoint interp_hyps (hs : list Prop) : Prop := 
  match hs with 
  | [] => 
    True
  | h :: hs => 
    h -> interp_hyps hs
  end.

Definition interp_wh (x: WithHyps) : Prop := 
  interp_hyps x.(hyps) -> x.(p).

Lemma interp_hyps_sound : 
  forall P, 
    P <-> interp_wh (WrapHyps [] P).
Proof.
  intros;
  compute;
  intuition eauto.
Qed.

Lemma add_hyp : 
  forall (hs : list Prop) (H P : Prop), 
    H -> 
    (interp_wh (WrapHyps hs P) <-> interp_wh (WrapHyps (H :: hs) P)).
Proof.
  unfold interp_wh.
  induction hs.
  - compute. 
    intuition eauto.
  - intros.
    simpl in *.
    intuition eauto.
Qed.

Lemma weaken_hyps : 
  forall (P: Prop) hs, 
    P -> interp_wh (WrapHyps hs P).
Proof.
  intros;
  compute;
  intuition eauto.
Qed.

Register WrapHyps as ms.hyps.wrap_hyps.
Register interp_hyps as ms.hyps.interp_hyps.
Register interp_wh as ms.hyps.interp_wh.
  


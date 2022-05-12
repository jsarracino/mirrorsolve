From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.

Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.

Import ListNotations.
Import HListNotations.

Set Universe Polymorphism.

Section Sum. 
  Variable (t_l : Type).
  Variable (t_r : Type).

  Inductive t := | Inl : t_l -> t | Inr : t_r -> t.

  Variable (l_eqdec : EquivDec.EqDec t_l eq).
  Variable (r_eqdec : EquivDec.EqDec t_r eq).

  Definition t_eqdec : EquivDec.EqDec t eq.
    unfold EquivDec.EqDec, Equivalence.equiv, RelationClasses.complement in *.
    intros.
    destruct x; destruct y.
    - destruct (l_eqdec t0 t1).
      + left; f_equal; trivial.
      + right; intros.
        inversion H.
        intuition eauto.
    - right; intros; inversion H.
    - right; intros; inversion H.
    - destruct (r_eqdec t0 t1).
      + left; f_equal; trivial.
      + right; intros; inversion H; intuition eauto.
  Defined.

End Sum.

Arguments Inl {_ _} _.
Arguments Inr {_ _} _.

Arguments t_eqdec {_ _} _ _.

Section SumTheory.

  Variable (l: signature).
  Variable (r: signature).

  Variable (ls_eq_dec : EquivDec.EqDec l.(sig_sorts) eq).
  Variable (rs_eq_dec : EquivDec.EqDec r.(sig_sorts) eq).

  Definition sorts := Sum.t l.(sig_sorts) r.(sig_sorts).

  Definition sorts_eq_dec : EquivDec.EqDec sorts eq := Sum.t_eqdec ls_eq_dec rs_eq_dec.

  Inductive funs : arity sorts -> sorts -> Type := 
  | LFun : forall {lsa lsr}, 
    l.(sig_funs) lsa lsr -> 
    funs (map Inl lsa) (Inl lsr)
  | RFun : forall {rsa rsr}, 
    r.(sig_funs) rsa rsr -> 
    funs (map Inr rsa) (Inr rsr).

  Inductive rels: arity sorts -> Type :=
  | LRel : forall {lsa}, 
    l.(sig_rels) lsa -> 
    rels (map Inl lsa)
  | RRel : forall {rsa}, 
    r.(sig_rels) rsa -> 
    rels (map Inr rsa).

  Definition sig: signature :=
    {| sig_sorts := sorts;
      sig_funs := funs;
      sig_rels := rels |}.

  Definition fm ctx := FirstOrder.fm sig ctx.
  Definition tm ctx := FirstOrder.tm sig ctx.

  Variable (mod_l : model l).
  Variable (mod_r : model r).

  Definition mod_sorts (s: sig_sorts sig) : Type :=
    match s with
    | Inl sl => mod_l.(mod_sorts _) sl
    | Inr sr => mod_r.(mod_sorts _) sr
    end.

  Equations strip_hl_inl {L R} {f: (Sum.t L R) -> Type} (x: list L) (args: HList.t f (map Inl x)) : HList.t (fun x => f (Inl x)) x := 
  { 
    strip_hl_inl nil hnil := hnil;
    strip_hl_inl (x :: xs) (v ::: vs) := v ::: strip_hl_inl xs vs;
  }.

  Equations strip_hl_inr {L R} {f: (Sum.t L R) -> Type} (x: list R) (args: HList.t f (map Inr x)) : HList.t (fun x => f (Inr x)) x := 
  { 
    strip_hl_inr nil hnil := hnil;
    strip_hl_inr (x :: xs) (v ::: vs) := v ::: strip_hl_inr xs vs;
  }.

  Arguments strip_hl_inl {_ _ _ _} _.
  Arguments strip_hl_inr {_ _ _ _} _.

  Definition mod_fns params ret (f: sig_funs sig params ret) (args: HList.t mod_sorts params) :=
    match f in funs a s return HList.t mod_sorts a -> mod_sorts s with 
    | LFun f' => fun args' => mod_fns _ _ _ _ f' (strip_hl_inl args')
    | RFun f' => fun args' => mod_fns _ _ _ _ f' (strip_hl_inr args')
    end args.

  Definition mod_rels params (f: sig_rels sig params) (args: HList.t mod_sorts params) : Prop :=
    match f in rels a return HList.t mod_sorts a -> Prop with 
    | LRel f' => fun args' => mod_rels _ _ _ f' (strip_hl_inl args')
    | RRel f' => fun args' => mod_rels _ _ _ f' (strip_hl_inr args')
    end args.

  Definition fm_model : model sig := {|
    FirstOrder.mod_sorts := mod_sorts;
    FirstOrder.mod_fns := mod_fns;
    FirstOrder.mod_rels := mod_rels;
  |}.

End SumTheory.


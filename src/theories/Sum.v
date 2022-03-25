From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.

Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.

Import ListNotations.
Import HListNotations.

Set Universe Polymorphism.
Section Sum.

  Variable (l: signature).
  Variable (r: signature).

  Variable (ls_eq_dec : EquivDec.EqDec l.(sig_sorts) eq).
  Variable (rs_eq_dec : EquivDec.EqDec r.(sig_sorts) eq).

  Definition sorts := (l.(sig_sorts) + r.(sig_sorts))%type.

  Definition sorts_eq_dec : EquivDec.EqDec sorts eq := sum_eqdec ls_eq_dec rs_eq_dec.

  Set Universe Polymorphism.

  Inductive funs : arity sorts -> sorts -> Type := 
  | LFun : forall {lsa lsr}, 
    l.(sig_funs) lsa lsr -> 
    funs (map inl lsa) (inl lsr)
  | RFun : forall {rsa rsr}, 
    r.(sig_funs) rsa rsr -> 
    funs (map inr rsa) (inr rsr).

  Inductive rels: arity sorts -> Type :=
  | LRel : forall {lsa}, 
    l.(sig_rels) lsa -> 
    rels (map inl lsa)
  | RRel : forall {rsa}, 
    r.(sig_rels) rsa -> 
    rels (map inr rsa).

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
    | inl sl => mod_l.(mod_sorts _) sl
    | inr sr => mod_r.(mod_sorts _) sr
    end.

  Equations strip_hl_inl {L R} {f: (L + R)%type -> Type} (x: list L) (args: HList.t f (map inl x)) : HList.t (fun x => f (inl x)) x := 
  { 
    strip_hl_inl nil hnil := hnil;
    strip_hl_inl (x :: xs) (v ::: vs) := v ::: strip_hl_inl xs vs;
  }.

  Equations strip_hl_inr {L R} {f: (L + R)%type -> Type} (x: list R) (args: HList.t f (map inr x)) : HList.t (fun x => f (inr x)) x := 
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

End Sum.


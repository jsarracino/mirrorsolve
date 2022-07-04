From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.

Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.

Import ListNotations.
Import HListNotations.

Set Universe Polymorphism.
Section Groups.
  (*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
  Variable (G: Type).
  Variable (e: G).
  Variable (f: G -> G -> G).
  Variable (i: G -> G).

  Inductive sorts : Set := | G'.

  Scheme Equality for sorts.
  Set Universe Polymorphism.

  Inductive funs: arity sorts -> sorts -> Type :=
    | e_f : funs [] G'
    | f_f : funs [G'; G'] G'
    | i_f : funs [G'] G'.

  Inductive rels: arity sorts -> Type :=.

  Definition sig: signature :=
    {| sig_sorts := sorts;
      sig_funs := funs;
      sig_rels := rels |}.

  Definition fm ctx := FirstOrder.fm sig ctx.
  Definition tm ctx := FirstOrder.tm sig ctx.

  Definition mod_sorts (s: sig_sorts sig) : Type :=
    match s with
    | G' => G
    end.

  Obligation Tactic := idtac.
  Equations 
    mod_fns {params ret} (f: sig_funs sig params ret) (args: HList.t mod_sorts params) 
    : mod_sorts ret :=
    { 
      mod_fns e_f _ := e;
      mod_fns f_f (l ::: r ::: _) := f l r;
      mod_fns i_f (x ::: _) := i x;
    }.

  Definition mod_rels params
    (args: sig_rels sig params)
    (env: HList.t mod_sorts params) : Prop :=
    match args with
    end.

  Arguments mod_fns _ _ _ _ : clear implicits.

  Program Definition fm_model : model sig := {|
    FirstOrder.mod_sorts := mod_sorts;
    FirstOrder.mod_fns := mod_fns;
    FirstOrder.mod_rels := mod_rels;
  |}.
  (*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

End Groups.


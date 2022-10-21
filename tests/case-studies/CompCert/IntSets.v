
  
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

Require Import String.
Require Import ZArith.
Require Import Znumtheory.
Require Import List.
Require Import Bool.
Require Import Lia.


Require Import MirrorSolve.FirstOrder.

Require Import MirrorSolve.BV.
Require Import MirrorSolve.SMT.
Require Import MirrorSolve.UF.

Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.
Require Import MirrorSolve.Reflection.Tactics.
From Hammer Require Import Hammer.

Require Import MirrorSolve.Crush.

Ltac hammer' := timeout 60 hammer.
Ltac crush' := timeout 60 crush.



Section IntvSets.


  (*** MS BEGIN {"type": "definition"} *)
  Inductive t := Nil | Cons (lo hi: Z) (tl: t).

  Hint Constructors t.

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
  
  Hint Constructors ok.

  Equations mem (x: Z) (s: t) : bool := {
    mem _ Nil := false;
    mem x (Cons l h s') := ite (Z.ltb x h) (Z.leb l x) (mem x s');
  }.

  Equations contains (L H: Z) (s: t) : bool := {
    contains _ _ Nil := false;
    contains L H (Cons l h s') := (Z.leb H h && Z.leb l L) || contains L H s';
  }.

  Equations add (L H: Z) (s: t) : t := {
    add L H Nil := Cons L H Nil;
    add L H (Cons l h s') := 
      ite (Z.ltb h L) (Cons l h (add L H s')) (
      ite (Z.ltb H l) (Cons L H (Cons l h s'))
        (add (Z.min l L) (Z.max h H) s'));
  }.
  
  Equations remove (L H: Z) (s: t) : t := {
    remove _ _ Nil := Nil ;
    remove L H (Cons l h s') := 
      ite (Z.ltb h L) (Cons l h (remove L H s'))
      (ite (Z.ltb H l) (Cons l h s')
      (ite (Z.ltb l L)
        (ite (Z.ltb H h) (Cons l L (Cons H h s')) (Cons l L (remove L H s')))
        (ite (Z.ltb H h) (Cons H h s') (remove L H s'))))
  }.

  Fixpoint inter (s1 s2: t) {struct s1} : t :=
    let fix intr (s2: t) : t :=
      match s1, s2 with
      | Nil, _ => Nil
      | _, Nil => Nil
      | Cons l1 h1 s1', Cons l2 h2 s2' =>
          if Z.leb h1 l2 then inter s1' s2
          else if Z.leb h2 l1 then intr s2'
          else if Z.leb l1 l2 then
            if Z.leb h2 h1 then Cons l2 h2 (intr s2') else Cons l2 h1 (inter s1' s2)
          else
            if Z.leb h1 h2 then Cons l1 h1 (inter s1' s2) else Cons l1 h2 (intr s2')
      end
    in intr s2.
  
  Equations union (s1 s2: t) : t := {
    union Nil s2 := s2;
    union s1 Nil := s1;
    union (Cons l1 h1 s1') (Cons l2 h2 s2') := add l1 h1 (add l2 h2 (union s1' s2'))
  }.

  Equations beq (s1 s2: t) : bool := {
    beq Nil Nil := true;
    beq (Cons l1 h1 t1) (Cons l2 h2 t2) := Z.eqb l1 l2 && Z.eqb h1 h2 && beq t1 t2;
    beq _ _ := false;
  }.
  (*** MS END {"type": "definition"} *)

  (*** MS EFFORT {"type": "lemma"} *)
  (*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
  Lemma in_nil: 
    forall z, 
      In z Nil <-> False.
  Proof. 
    intros; simpl; intuition. 
  Qed.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma in_cons: 
    forall x l h t, 
      (l <= x < h \/ In x t) <->
      In x (Cons l h t).
  Proof. intros; simpl; intuition. Qed.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma ok_nil': 
    ok Nil <-> True.
  Proof.
    intuition eauto.
  Qed.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma ok_cons': 
    forall l h t, 
      (l < h /\ (forall x, In x t -> h < x) /\ ok t) <->
      ok (Cons l h t).
  Proof.
    intuition eauto;
    match goal with 
    | H: ok _ |- _ => 
      inversion H; subst; clear H
    end;
    intuition eauto.
  Qed.

  Local Declare ML Module "mirrorsolve".

  From MetaCoq.Template Require Import All Loader.
  Import MCMonadNotation.
  Require Import MirrorSolve.Config.
  Open Scope bs.

  (* Unset Universe Polymorphism. *)

  (* MirrorSolve's automation needs this later. *)
  Universe foo.
  MetaCoq Quote Definition typ_term := Type@{foo}.

  
  Notation pack x := (existT _ _ x).

  Definition fun_syms : list Config.packed := ([
      pack IntvSets.mem
    ; pack IntvSets.contains
    ; pack IntvSets.add
    ; pack IntvSets.remove
    ; pack IntvSets.union
    ; pack IntvSets.beq
    ; pack IntvSets.t
    ; pack Z.ltb
    ; pack Z.leb
    ; pack (@ite t)
    ; pack Z.max
    ; pack Z.min
    ; pack orb
    ; pack andb
    ; pack (@ite Z)
    ; pack (@ite bool)
    ; pack inter
    ; pack Z.eqb
  ])%type.

  Definition rel_syms : list Config.packed := ([ 
      pack IntvSets.In
    ; pack IntvSets.ok
    ; pack Z.lt
    ; pack Z.gt
    ; pack Z.le
  ])%type.

  Definition prim_syms : list (Config.packed * String.string) := [
      (pack Z.lt, "<"%string)
    ; (pack Z.gt, ">"%string)
    ; (pack Z.ltb, "<"%string)
    ; (pack Z.gtb, ">"%string)
    ; (pack Z.le, "<="%string)
    ; (pack Z.leb, "<="%string)
    ; (pack Z.eqb, "="%string)
    ; (pack (@ite Z), "ite"%string)
    ; (pack (@ite t), "ite"%string)
    ; (pack (@ite bool), "ite"%string)
    ; (pack orb, "or"%string)
    ; (pack andb, "and"%string)
  ].

  MetaCoq Run (
    xs <- add_funs typ_term fun_syms rel_syms ;;
    xs' <- tmQuote xs ;;
    tmMkDefinition "trans_tbl" xs'
  ).

  MetaCoq Run (
    gen_sig typ_term sorts fol_funs fol_rels 
  ).
  MetaCoq Run (
    gen_interp_funs sorts interp_sorts fol_funs trans_tbl
  ).
  MetaCoq Run (
    gen_interp_rels sorts interp_sorts fol_rels trans_tbl
  ).
  Definition fm_model := Build_model sig interp_sorts interp_funs interp_rels.
  MetaCoq Run (
    match Utils.find _ _ smt_fun_base_beq IntLit (Utils.flip trans_tbl.(mp_consts)) with 
    | Some v => add_const_wf_instance sig fm_model v IntLit 
    | None => tmReturn tt
    end
  ).
  MetaCoq Run (
    match Utils.find _ _ smt_fun_base_beq BoolLit (Utils.flip trans_tbl.(mp_consts)) with 
    | Some v => add_const_wf_instance sig fm_model v BoolLit 
    | None => tmReturn tt
    end
  ).
  MetaCoq Run (
    add_matches sig fm_model trans_tbl
  ).
  MetaCoq Run (
    ctx <- build_printing_ctx sig sort_Prop trans_tbl prim_syms;; 
    ctx' <- tmEval all ctx ;;
    rhs <- tmQuote ctx' ;; 
    tmMkDefinition "fol_theory" rhs
  ).

  Require Import MirrorSolve.Reflection.Tactics.

  Transparent denote_tm.
  Require Import MirrorSolve.Axioms.

  (* We make use of the verification trick of negating the goal and checking for unsat. 
    The check_unsat_neg tactic behaves like idtac if the negated goal is unsat and otherwise fails.
    *)
  Ltac check_goal_unsat := 
    match goal with 
    | |- ?G => check_unsat_neg_func fol_theory G; eapply UnsoundAxioms.interp_true
    end.

  Create HintDb intvsets_eqns.

  Ltac prep_proof := 
    hints_foreach (fun x => pose proof x) "intvsets_eqns";
    Utils.revert_all;
    unfold "<->" in *.

  Scheme Equality for sorts.

  Ltac quote_reflect_intvsets := quote_reflect sig fm_model sorts_eq_dec match_tacs match_sorts.

  Ltac mirrorsolve :=
    timeout 60 (prep_proof;
    quote_reflect_intvsets;
    check_goal_unsat).


  (*** MS EFFORT {"type": "lemma"} *)
  Lemma z_max_eq: 
    forall x y, Z.max x y = ite (Z.ltb x y) y x.
  Proof.
    intros.
    destruct (_ <? _)%Z eqn:?;
    simpl;
    lia.
  Qed.
  (*** MS EFFORT {"type": "lemma"} *)
  Lemma z_min_eq: 
    forall x y, Z.min x y = ite (Z.ltb x y) x y.
  Proof.
    intros.
    destruct (_ <? _)%Z eqn:?;
    simpl;
    lia.
  Qed.

  Hint Immediate z_max_eq : intvsets_eqns.
  Hint Immediate z_min_eq : intvsets_eqns.

  Hint Immediate mem_equation_1 : intvsets_eqns.
  Hint Immediate mem_equation_2 : intvsets_eqns.

  Hint Immediate in_nil : intvsets_eqns.
  Hint Immediate in_cons : intvsets_eqns.

  Hint Immediate ok_nil' : intvsets_eqns.
  Hint Immediate ok_cons': intvsets_eqns.

  SetSMTSolver "cvc5".

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 1} *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma mem_In:
    forall x s, 
      ok s -> 
      (mem x s = true <-> IntvSets.In x s).
  (*** MS END {"type": "proof_definition"} *)
  Proof.
    induction s;
    try hammer'.
    Restart.
    induction s;
    try crush'.
    Restart.
    induction s;
    mirrorsolve.
  Qed.

  Hint Immediate mem_In : intvsets_eqns.

  Hint Immediate contains_equation_1 : intvsets_eqns.
  Hint Immediate contains_equation_2 : intvsets_eqns.

  SetSMTSolver "z3".

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 2, "ms": 2, "hammer": 0, "crush": 1} *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma contains_In:
    forall l0 h0, 
      l0 < h0 -> 
      forall s, ok s ->
    (contains l0 h0 s = true <-> (forall x, l0 <= x < h0 -> IntvSets.In x s)).
  (*** MS END {"type": "proof_definition"} *)
  Proof.
    induction 2;
    try hammer'.
    Restart.
    induction 2.
    - crush'.
    - crush';
      admit.
    Restart.
    induction 2;
    mirrorsolve.
  Qed.

  Hint Immediate contains_In : intvsets_eqns.
  Hint Immediate add_equation_1 : intvsets_eqns.
  Hint Immediate add_equation_2 : intvsets_eqns.

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 0} *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma In_add:
    forall x s, 
      ok s -> 
      forall l0 h0, 
        (IntvSets.In x (add l0 h0 s) <-> l0 <= x < h0 \/ IntvSets.In x s).
  (*** MS END {"type": "proof_definition"} *)
  Proof.
    induction s;
    try hammer'.
    Restart.
    induction s.
    - crush';
      admit.
    - crush';
      admit.
    Restart.
    induction s;
    mirrorsolve.
  Qed.

  Hint Immediate In_add : intvsets_eqns.



  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 2, "ms": 2, "hammer": 0, "crush": 0} *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma add_ok:
    forall s, 
      ok s -> 
      forall l0 h0, 
        l0 < h0 -> 
        ok (add l0 h0 s).
  (*** MS END {"type": "proof_definition"} *)
  Proof.
    induction s;
    try hammer'.
    Restart.
    induction s.
    - crush'.
      admit.
    - crush';
      admit.
    Restart.
    SetSMTSolver "cvc5".
    induction s;
    try mirrorsolve.
  Qed.

  Hint Immediate add_ok : intvsets_eqns.

  Hint Immediate remove_equation_1 : intvsets_eqns.
  Hint Immediate remove_equation_2 : intvsets_eqns.


  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 1} *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma In_remove:
    forall x l0 h0 s, 
      ok s ->
      (IntvSets.In x (IntvSets.remove l0 h0 s) <-> ~(l0 <= x < h0) /\ IntvSets.In x s).
  (*** MS END {"type": "proof_definition"} *)
  Proof.
    induction s;
    try hammer'.
    Restart.
    induction s.
    - crush'.
    - crush';
      admit.
    Restart.
    induction s;
    try mirrorsolve.
  Qed.

  Hint Immediate In_remove : intvsets_eqns.

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 1} *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma remove_ok:
    forall l0 h0, 
      l0 < h0 -> 
        forall s, 
          ok s -> 
          ok (IntvSets.remove l0 h0 s).
  (*** MS END {"type": "proof_definition"} *)
  Proof.
    induction s;
    try hammer'.
    Restart.
    induction s.
    - crush'.
    - crush';
      admit.
    Restart.
    induction s;
    try mirrorsolve.
  Qed.


  (*** MS EFFORT {"type": "lemma"} *)
  Lemma inter_equation_1 : 
    forall x, inter Nil x = Nil.
  Proof. 
    induction x;
    intuition eauto.
  Qed.
  (*** MS EFFORT {"type": "lemma"} *)
  Lemma inter_equation_2 : 
    forall x, inter x Nil = Nil.
  Proof. 
    induction x;
    intuition eauto.
  Qed.

  Hint Immediate inter_equation_1 : intvsets_eqns.
  Hint Immediate inter_equation_2 : intvsets_eqns.


  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": False, "ho": False, "goals": 4, "ms": 3, "hammer": 3, "crush": 3} *)
  Lemma In_inter:
    forall x s1, ok s1 -> forall s2, ok s2 ->
    (IntvSets.In x (inter s1 s2) <-> IntvSets.In x s1 /\ IntvSets.In x s2).
  Proof.
    induction 1;
    induction 1;
    try hammer'.
    Restart.
    induction 1;
    induction 1.
    - crush'.
    - crush'.
    - crush'.
    - crush';
      admit.
    Restart.
    induction 1;
    induction 1;
    try mirrorsolve.
  Admitted.

  Hint Immediate In_inter : intvsets_eqns.


  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": False, "ho": False, "goals": 4, "ms": 3, "hammer": 3, "crush": 3} *)
  Lemma inter_ok:
    forall s1, ok s1 -> forall s2, ok s2 -> ok (inter s1 s2).
  Proof.
    induction 1;
    induction 1;
    try hammer'.
    Restart.
    induction 1;
    induction 1.
    - crush'.
    - crush'.
    - crush'.
    - crush';
      admit.
    Restart.
    induction 1;
    induction 1;
    try mirrorsolve.
  Admitted.

  Hint Immediate inter_ok : intvsets_eqns.

  Hint Immediate union_equation_1 : intvsets_eqns.
  Hint Immediate union_equation_2 : intvsets_eqns.
  Hint Immediate union_equation_3 : intvsets_eqns.
  

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 4, "ms": 4, "hammer": 3, "crush": 1} *)
    
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
    induction 1;
    induction 1;
    try hammer'.
    Restart.
    induction 1;
    induction 1.
    - crush'.
    - crush'; 
      admit.
    - crush'; 
      admit.
    - crush';
      admit.
    Restart.
    induction 1;
    induction 1;
    try mirrorsolve.
  Qed.



  Hint Immediate In_ok_union : intvsets_eqns.
  Hint Immediate beq_equation_1 : intvsets_eqns.
  Hint Immediate beq_equation_2 : intvsets_eqns.
  Hint Immediate beq_equation_3 : intvsets_eqns.
  Hint Immediate beq_equation_4 : intvsets_eqns.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals": 4, "ms": 4, "hammer": 3, "crush": 3} *)
  Lemma beq_eq : 
    forall x y, beq x y = true <-> x = y.
  Proof.
    induction x;
    induction y;
    try hammer'.
    Restart.
    induction x;
    induction y.
    - try crush'.
    - try crush'.
    - crush'.
    - 
      (* crush'. *)
      admit.
    Restart.
    induction x;
    induction y;
    try mirrorsolve.
  Qed.

  Hint Immediate beq_eq : intvsets_eqns.

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 4, "ms": 3, "hammer": 1, "crush": 3} *)
    
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma beq_spec:
    forall s1,  
      ok s1 -> 
      forall s2, 
        ok s2 ->
        (beq s1 s2 = true <-> (forall x, IntvSets.In x s1 <-> IntvSets.In x s2)).
  (*** MS END {"type": "proof_definition"} *)
  Proof.

    induction 1; 
    induction 1.
    - mirrorsolve.
    - SetSMTSolver "z3".
      mirrorsolve.
    - SetSMTSolver "cvc5".
      mirrorsolve.
    - admit.
    Restart.
    induction 1;
    induction 1;
    try hammer'.
    Restart.
    induction 1;
    induction 1.
    - crush'.
    - crush'.
    - crush'.
    - 
      (* crush'. *)
      admit.
  Admitted.

End IntvSets.





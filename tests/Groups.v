
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

Section Groups.

  Unset Universe Polymorphism.
  (* The set of the group. *)
  (*** MS BEGIN {"type": "definition"} *)
  Variable G : Set.
  (*** MS END {"type": "definition"} *)

  (* The binary operator. *)
  
  (*** MS EFFORT {"type": "definition"} *)
  (*** MS BEGIN {"type": "definition"} *)
  Variable f : G -> G -> G.
  Definition f' := f.
  (*** MS END {"type": "definition"} *)

  (* The group identity. *)
  (*** MS EFFORT {"type": "definition"} *)
  (*** MS BEGIN {"type": "definition"} *)
  Variable e : G.
  Definition e' := e.
  (*** MS END {"type": "definition"} *)

  (* The inverse operator. *)
  (*** MS EFFORT {"type": "definition"} *)
  (*** MS BEGIN {"type": "definition"} *)
  Variable i : G -> G.
  Definition i' := i.
  (*** MS END {"type": "definition"} *)

  (* For readability, we use infix <+> to stand for the binary operator. *)
  Infix "<+>" := f' (at level 50, left associativity).

  (* The operator [f] is associative. *)
  (*** MS EFFORT {"type": "edit"} *)
  (*** MS BEGIN {"type": "definition"} *)
  Axiom assoc : forall a b c, a <+> b <+> c = a <+> (b <+> c).
  (*** MS END {"type": "definition"} *)

  (* [e] is the right-identity for all elements [a] *)
  (*** MS EFFORT {"type": "edit"} *)
  (*** MS BEGIN {"type": "definition"} *)
  Axiom id_r : forall a, a <+> e' = a.
  (*** MS END {"type": "definition"} *)

  (*** MS EFFORT {"type": "edit"} *)
  (* [i a] is the right-inverse of [a]. *)
  (*** MS BEGIN {"type": "definition"} *)
  Axiom inv_r : forall a, a <+> i' a = e'.
  (*** MS END {"type": "definition"} *)

  (* encoding groups in in FOL *)

  Local Declare ML Module "mirrorsolve".

  From MetaCoq.Template Require Import All Loader.
  Import MCMonadNotation.
  Require Import MirrorSolve.Config.
  Require Import Coq.Lists.List.
  Import ListNotations.
  Open Scope bs.

  Universe foo.
  MetaCoq Quote Definition typ_term := Type@{foo}.
  
  Notation pack x := (existT _ _ x).

  Definition fun_syms : list Config.packed := ([
      pack f'
    ; pack e'
    ; pack i'
  ])%type.

  Definition rel_syms : list Config.packed := ([ 
  ])%type.

  Definition prim_syms : list (Config.packed * String.string) := [
  ].

  MetaCoq Run (
    xs <- add_funs typ_term fun_syms [] ;;
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

  Create HintDb groups_eqns.

  Ltac prep_proof := 
    hints_foreach (fun x => pose proof x) "groups_eqns";
    Utils.revert_all;
    unfold "<->" in *.

  Scheme Equality for sorts.

  Ltac quote_reflect_groups := quote_reflect sig fm_model sorts_eq_dec match_tacs match_sorts.

  Ltac mirrorsolve :=
    timeout 60 (prep_proof;
    quote_reflect_groups;
    check_goal_unsat).

  Set MirrorSolve Solver "z3".
  (*** MS END {"type": "configuration", "config_type":"tactics"} *)


  Hint Immediate assoc : groups_eqns.
  Hint Immediate inv_r : groups_eqns.
  Hint Immediate id_r : groups_eqns.

  Hint Transparent f'.
  Hint Transparent e'.
  Hint Transparent i'.

  Hint Resolve assoc.
  Hint Resolve inv_r.
  Hint Resolve id_r.

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 1} *)
  Lemma mult_both : 
    forall a b c d1 d2, 
      a <+> c = d1
      -> b <+> c = d2
      -> a = b
      -> d1 = d2.
  Proof.
    crush'.
    Restart.
    hammer'.
    Restart.
    mirrorsolve.
  Qed.

  Hint Extern 100 (_ = _) =>
  match goal with
    | [ _ : True |- _ ] => fail 1
    | _ => assert True by constructor; eapply mult_both 
  end.

  (*** MS LEMMA {"original": False, "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 0} *)
  Lemma add_right : 
    forall a b c, 
      a <+> b = a <+> c -> 
      a <+> b <+> i' b = a <+> c <+> i' c.
  Proof.
    crush'.
    Restart.
    hammer'.
    Restart.
    mirrorsolve.
  Qed.

  Hint Immediate add_right : groups_eqns.
  Hint Resolve add_right.

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 0} *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma unique_id : 
    forall a, 
      a <+> a = a -> 
      a = e'.
  (*** MS END {"type": "proof_definition"} *)
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
    mirrorsolve.
  Qed.

  Hint Immediate unique_id : groups_eqns.
  Hint Resolve unique_id.

  (* [i a] is the left-inverse of [a]. *)
  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 0} *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma inv_l : 
    forall a, 
      i' a <+> a = e'.
  (*** MS END {"type": "proof_definition"} *)
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
    mirrorsolve.
  Qed.

  Hint Immediate inv_l : groups_eqns.
  Hint Resolve inv_l.


  (* [e] is the left-identity. *)
  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 0} *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma id_l : 
    forall a, 
      e' <+> a = a.
      (*** MS END {"type": "proof_definition"} *)
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
    mirrorsolve.
  Qed.

  Hint Immediate id_l : groups_eqns.
  Hint Resolve id_l.

  (*** MS LEMMA {"original": False , "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 0} *)
  Lemma cancel_inv_r : 
    forall a b x, 
      a <+> x <+> i' x = b <+> x <+> i' x 
      -> a = b.
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
    Set MirrorSolve Solver "z3".
    mirrorsolve.
  Qed.

  Hint Resolve cancel_inv_r.
  Hint Immediate cancel_inv_r : groups_eqns.



  (* [x] can be cancelled on the right. *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 0, "crush": 0} *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma cancel_r : 
    forall a b x, 
      a <+> x = b <+> x -> 
      a = b.
      (*** MS END {"type": "proof_definition"} *)
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
    mirrorsolve.
  Qed.

  Hint Immediate cancel_r : groups_eqns.
  Hint Resolve cancel_r.

  (*** MS LEMMA {"original": False , "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 0} *)
  Lemma cancel_inv_l : 
    forall a b x, 
      x <+> i' x <+> a = x <+> i' x <+> b ->
      a = b.
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
    mirrorsolve.
  Qed.

  Hint Resolve cancel_inv_l.
  Hint Immediate cancel_inv_l : groups_eqns.

  (* [x] can be cancelled on the left. *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 0} *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma cancel_l: 
    forall a b x, 
      x <+> a = x <+> b -> 
      a = b.
    (*** MS END {"type": "proof_definition"} *)
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
    try mirrorsolve.
  Qed.

  Hint Immediate cancel_l : groups_eqns.
  Hint Resolve cancel_l : groups_eqns.

  (* The left identity is unique. *)
  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 0} *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma e_uniq_l : 
    forall a p, 
      p <+> a = a -> 
      p = e'.
    (*** MS END {"type": "proof_definition"} *)
  Proof. 
    try hammer'.
    Restart.
    try crush'.
    Restart.
    try mirrorsolve.
  Qed.

  Hint Immediate e_uniq_l : groups_eqns.
  Hint Resolve e_uniq_l.

  (* The left inverse is unique. *)
  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 0} *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma inv_uniq_l : 
    forall a b, 
      a <+> b = e' -> 
      a = i' b.
    (*** MS END {"type": "proof_definition"} *)
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
    try mirrorsolve.
  Qed.

  Hint Immediate inv_uniq_l : groups_eqns.
  Hint Resolve inv_uniq_l.

  (* The right identity is unique. *)
  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 0} *)
  
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma e_uniq_r : 
    forall a p, 
      a <+> p = a -> 
      p = e'.
    (*** MS END {"type": "proof_definition"} *)
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
    try mirrorsolve.
  Qed.

  Hint Immediate e_uniq_r : groups_eqns.
  Hint Resolve e_uniq_r.

  (* The right inverse is unique. *)
  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 0} *)
  
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma inv_uniq_r : 
    forall a b, 
      a <+> b = e' -> 
      b = i' a.
    (*** MS END {"type": "proof_definition"} *)
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
    try mirrorsolve.
  Qed.

  Hint Immediate inv_uniq_r : groups_eqns.
  Hint Resolve inv_uniq_r.

  (* The right inverse is unique. *)

  (* The inverse operator distributes over the group operator. *)
   (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 0} *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma inv_distr : 
    forall a b, 
      i' (a <+> b) = i' b <+> i' a.
      (*** MS END {"type": "proof_definition"} *)
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
    try mirrorsolve.
  Qed.

  Hint Immediate inv_distr : groups_eqns.
  Hint Resolve inv_distr.

  (* The inverse of an inverse produces the original element. *)
   (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 0} *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma double_inv : 
    forall a, 
      i' (i' a) = a.
    (*** MS END {"type": "proof_definition"} *)
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
    try mirrorsolve.
  Qed.

  Hint Immediate double_inv : groups_eqns.
  Hint Resolve inv_distr.

  (* The identity is its own inverse. *)
   (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 0} *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma id_inv : 
    i' e' = e'.
    (*** MS END {"type": "proof_definition"} *)
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
    try mirrorsolve.
  Qed.

End Groups.
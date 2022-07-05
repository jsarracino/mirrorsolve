
(** * SearchTree: Binary Search Trees *)
(* Due to VFA's exercise on binary search trees: 
  https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html
*)

Require Import MirrorSolve.FirstOrder.

Require Import MirrorSolve.BV.
Require Import MirrorSolve.SMT.
Require Import MirrorSolve.UF.

Require Import MirrorSolve.FOLTrees.

Require Import MirrorSolve.HLists.
Require Import Coq.Lists.List.

Import HListNotations.
Import ListNotations.

Require Import Coq.Strings.String.

Require Import Coq.ZArith.BinInt.
Import HListNotations.

Require Import MirrorSolve.BV.
Require Import MirrorSolve.SMT.
Require Import MirrorSolve.UF.

Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.
Require Import MirrorSolve.Reflection.Tactics.
From Hammer Require Import Hammer.

Set Hammer ATPLimit 5.
Set Hammer ReconstrLimit 10.

Section Trees.
  (* type of values in the tree *)
  Variable (V: Type).
  Set Universe Polymorphism.

  (*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
  
  Notation sig := FOLTrees.sig.
  
  Definition tree_model := FOLTrees.fm_model V.

  MetaCoq Quote Definition t_ite := @ite.
  MetaCoq Quote Definition t_zlt := @Z.ltb.
  MetaCoq Quote Definition t_glt := @Z.gtb.
  MetaCoq Quote Definition t_zlt' := @Z.lt.
  MetaCoq Quote Definition t_glt' := @Z.gt.
  MetaCoq Quote Definition t_emp := @Emp.
  MetaCoq Quote Definition t_node := @Node.
  MetaCoq Quote Definition t_insert := (@FOLTrees.insert V).
  MetaCoq Quote Definition t_lookup := (@FOLTrees.lookup V).
  MetaCoq Quote Definition t_bound := (@FOLTrees.bound V).
  MetaCoq Quote Definition t_lt_t := (@FOLTrees.lt_t V).
  MetaCoq Quote Definition t_gt_t := (@FOLTrees.gt_t V).
  MetaCoq Quote Definition t_ordered := (@FOLTrees.ordered V).
  
  Definition is_emp t := eq_ctor t t_emp.
  Definition is_node t := eq_ctor t t_node.
  Definition is_zlt t := eq_term t t_zlt.
  Definition is_zgt t := eq_term t t_glt.
  Definition is_insert t := eq_ctor t t_insert.
  Definition is_lookup t := eq_ctor t t_lookup.
  Definition is_bound t := eq_ctor t t_bound.
  Definition is_lt_t t := eq_ctor t t_lt_t.
  Definition is_gt_t t := eq_ctor t t_gt_t.
  Definition is_ordered t := eq_ctor t t_ordered.
  Definition is_zlt' t := eq_term t t_zlt'.
  Definition is_zgt' t := eq_term t t_glt'.

  MetaCoq Quote Definition t_bool := (bool).
  MetaCoq Quote Definition t_Z := (Z).
  MetaCoq Quote Definition t_tree := (@tree V).
  MetaCoq Quote Definition t_V := (V).

  Definition is_cond_b t :=
    match t with 
    | tApp f (t :: _) => 
      andb (eq_term f t_ite) (eq_term t t_bool)
    | _ => false
    end.

  Definition is_cond_t t :=
    match t with 
    | tApp f (t :: _) => 
      andb (eq_term f t_ite) (eq_term t t_V)
    | _ => false
    end.

  Definition is_cond_tree t :=
    match t with 
    | tApp f (t :: _) => 
      andb (eq_term f t_ite) (eq_term t t_tree)
    | _ => false
    end.

  Notation tac_bool := (tacLit sig tree_model bool_lit (fun b => (BS; b)) (fun b _ => (BS; TFun sig (b_lit b) hnil))).
  Notation tac_fun f := (tacFun _ _ (Mk_fun_sym sig _ _ f)).
  Notation tac_rel f := (tacRel _ _ (Mk_rel_sym sig _ f)).

  Definition match_tacs : list ((term -> bool) * tac_syn sig tree_model) := [
      ( is_emp, tac_fun e_f)
    ; ( is_node, tac_fun t_f)
    ; ( is_zlt, tac_fun z_lt)
    ; ( is_zgt, tac_fun z_gt)
    ; ( is_cond_b, tac_fun cond_b)
    ; ( is_cond_t, tac_fun cond_t)
    ; ( is_cond_tree, tac_fun cond_tree)
    ; ( is_bool_term, tac_bool )
    ; ( is_lookup, tac_fun lookup_f)
    ; ( is_bound, tac_fun bound_f)
    ; ( is_insert, tac_fun insert_f)
    ; ( is_lt_t, tac_rel lt_t_r)
    ; ( is_gt_t, tac_rel gt_t_r)
    ; ( is_ordered, tac_rel ordered_r) 
    ; ( is_zlt', tac_rel lt_z)
    ; ( is_zgt', tac_rel gt_z)
  ].

  Definition match_inds : list ((term -> bool) * FOLTrees.sorts) := [
      (eq_term t_tree, TreeS)
    ; (eq_term t_V, TS)
    ; (eq_term t_bool, BS)
    ; (eq_term t_Z, ZS)
  ].

  Local Declare ML Module "mirrorsolve".
  (*** MS END {"type": "configuration", "config_type":"boilerplate"} *)
  (*** MS BEGIN {"type": "configuration", "config_type":"plugin"} *)
  RegisterCustomSort TS "A".
  (*** MS END {"type": "configuration", "config_type":"plugin"} *)

  (*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
  RegisterSMTInd TreeS (SICases [
    ("node"%string, [SIRec; SISort (SInt tt); SISort (SCustom "A"); SIRec]); 
    ("emp"%string, [])
    ]) "A_tree".
  (*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

  (*** MS BEGIN {"type": "configuration", "config_type":"plugin"} *)

  RegisterSMTSort ZS SInt.
  RegisterSMTSort BS SBool.

  RegisterSMTUF "bound" BS ZS TreeS.
  RegisterSMTUF "lookup" TS TS ZS TreeS.
  RegisterSMTUF "insert" TreeS ZS TS TreeS.
  RegisterSMTUF "lt_t" BS ZS TreeS.
  RegisterSMTUF "gt_t" BS ZS TreeS.
  RegisterSMTUF "ordered" BS TreeS.

  RegisterSMTFun FOLTrees.z_lt "<" 2.
  RegisterSMTFun FOLTrees.z_gt ">" 2.
  RegisterSMTFun FOLTrees.lt_z "<" 2.
  RegisterSMTFun FOLTrees.gt_z ">" 2.
  RegisterSMTFun FOLTrees.e_f "emp" 0.
  RegisterSMTFun FOLTrees.t_f "node" 4.
  RegisterSMTFun FOLTrees.bound_f "bound" 2.
  RegisterSMTFun FOLTrees.lookup_f "lookup" 3.
  RegisterSMTFun FOLTrees.insert_f "insert" 3.
  RegisterSMTFun FOLTrees.lt_t_r "lt_t" 2.
  RegisterSMTFun FOLTrees.gt_t_r "gt_t" 2.
  RegisterSMTFun FOLTrees.ordered_r "ordered" 1.
  RegisterSMTFun FOLTrees.cond_b "ite" 3.
  RegisterSMTFun FOLTrees.cond_t "ite" 3.
  RegisterSMTFun FOLTrees.cond_tree "ite" 3.

  RegisterSMTBuiltin FOLTrees.b_lit BoolLit.
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
  Ltac pose_lookup_axioms := Utils.pose_all (tt, @lookup_emp V, @lookup_node V).
  Ltac pose_bound_axioms := Utils.pose_all (tt, @bound_emp V, @bound_node V).
  Ltac pose_insert_axioms := Utils.pose_all (tt, @insert_emp V, @insert_node V).
  Ltac pose_ordered_axioms := Utils.pose_all (tt, @lt_t_emp V, @lt_t_node V, @gt_t_emp V, @gt_t_node V, @ordered_emp V, @ordered_node V).

  Ltac pose_tree_axioms := pose_lookup_axioms; 
    pose_bound_axioms; 
    pose_insert_axioms; 
    pose_ordered_axioms.

  Ltac prep_proof := pose_tree_axioms; 
    Utils.revert_all; 
    unfold "<->" in *;
    intros V.

  Ltac reflect t := reflect_goal_trust FOLTrees.sig tree_model FOLTrees.sorts_eq_dec match_tacs match_inds t.
  (*** MS END {"type": "configuration", "config_type":"tactics"} *)

  (*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
  MetaCoq Quote Definition lookup_empty_goal := (
    (forall (d : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 lookup d x (Node l y v r) = ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 bound x (Node l y v r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v l) y v' r)
   (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
(forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
(forall (l : tree V) (k : Z) (v : V) (r : tree V),
 (lt_t k l /\ gt_t k r /\ ordered l /\ ordered r -> ordered (Node l k v r)) /\
 (ordered (Node l k v r) -> lt_t k l /\ gt_t k r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
 ((k' > k)%Z /\ gt_t k l /\ gt_t k r -> gt_t k (Node l k' v r)) /\
 (gt_t k (Node l k' v r) -> (k' > k)%Z /\ gt_t k l /\ gt_t k r)) ->
(forall k : Z, gt_t k Emp) ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
 ((k' < k)%Z /\ lt_t k l /\ lt_t k r -> lt_t k (Node l k' v r)) /\
 (lt_t k (Node l k' v r) -> (k' < k)%Z /\ lt_t k l /\ lt_t k r)) ->
(forall k : Z, lt_t k Emp) -> forall (d : V) (k : Z), lookup d k Emp = d
  ).
  (*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

  (* hammer handles this one (it's easy) *)
  (*** MS BEGIN {"type": "configuration", "config_type":"plugin"} *)
  SetSMTSolver "cvc5".
  (*** MS END {"type": "configuration", "config_type":"plugin"} *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Theorem lookup_empty : 
    forall (d: V) (k : Z),
      lookup d k Emp = d.
  (*** MS END {"type": "proof_definition"} *)
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
    intros.
    trivial.
    (*** MS END {"type": "proof", "proof_type":"manual"} *)
    Restart.
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
    hammer.
    (*** MS END {"type": "proof", "proof_type":"hammer", "total":1, "finished":1} *)
  Restart.
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
    prep_proof.
    reflect lookup_empty_goal; 
    check_goal_unsat.
    (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":1} *)
  Admitted. (* some weird evaluation issue, can't QED... *)

  (*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
  MetaCoq Quote Definition lookup_insert_emp := (
    
(forall (d : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
lookup d x (Node l y v r) = ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
bound x (Node l y v r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
insert x v (Node l y v' r) =
ite (x <? y)%Z (Node (insert x v l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
(forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
(forall (l : tree V) (k : Z) (v : V) (r : tree V),
(lt_t k l /\ gt_t k r /\ ordered l /\ ordered r -> ordered (Node l k v r)) /\
(ordered (Node l k v r) -> lt_t k l /\ gt_t k r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
((k' > k)%Z /\ gt_t k l /\ gt_t k r -> gt_t k (Node l k' v r)) /\
(gt_t k (Node l k' v r) -> (k' > k)%Z /\ gt_t k l /\ gt_t k r)) ->
(forall k : Z, gt_t k Emp) ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
((k' < k)%Z /\ lt_t k l /\ lt_t k r -> lt_t k (Node l k' v r)) /\
(lt_t k (Node l k' v r) -> (k' < k)%Z /\ lt_t k l /\ lt_t k r)) ->
(forall k : Z, lt_t k Emp) ->
forall (d : V) (k k' : Z) (v : V), k = k' -> lookup d k (insert k' v Emp) = v
).

  MetaCoq Quote Definition lookup_insert_node := (
    forall (t1 : tree V) (k : Z) (v : V) (t2 : tree V),
(forall (d : V) (k0 k' : Z) (v0 : V), k0 = k' -> lookup d k0 (insert k' v0 t1) = v0) ->
(forall (d : V) (k0 k' : Z) (v0 : V), k0 = k' -> lookup d k0 (insert k' v0 t2) = v0) ->
(forall (d : V) (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 lookup d x (Node l y v0 r) = ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v0)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 bound x (Node l y v0 r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v0 (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v0 l) y v' r)
   (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
(forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
(forall (l : tree V) (k0 : Z) (v0 : V) (r : tree V),
 (lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r -> ordered (Node l k0 v0 r)) /\
 (ordered (Node l k0 v0 r) -> lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r -> gt_t k0 (Node l k' v0 r)) /\
 (gt_t k0 (Node l k' v0 r) -> (k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r)) ->
(forall k0 : Z, gt_t k0 Emp) ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r -> lt_t k0 (Node l k' v0 r)) /\
 (lt_t k0 (Node l k' v0 r) -> (k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r)) ->
(forall k0 : Z, lt_t k0 Emp) ->
forall (d : V) (k0 k' : Z) (v0 : V), k0 = k' -> lookup d k0 (insert k' v0 (Node t1 k v t2)) = v0
  ).
  (*** MS END {"type": "configuration", "config_type":"boilerplate"} *)


  (*** MS BEGIN {"type": "proof_definition"} *)
  Theorem lookup_insert_eq : 
    forall (t : tree V) d k k' v,
      k = k' ->
      lookup d k (insert k' v t)  = v.
  (*** MS END {"type": "proof_definition"} *)
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
    induction t;
    intros;
    simpl in *;
    subst.
    - destruct (_ <? _)%Z eqn:?;
      simpl in *; [
          Lia.lia
        |
      ].
      destruct (_ >? _)%Z eqn:?;
      simpl in *; [
          Lia.lia
        | trivial
      ].
    - destruct (_ <? _)%Z eqn:?;
      simpl in *.
      * erewrite Heqb;
        simpl;
        eapply IHt1;
        trivial.
      * destruct (_ >? _)%Z eqn:?;
        try erewrite Heqb0;
        simpl in *;
        try erewrite Heqb;
        simpl;
        try erewrite Heqb0;
        simpl.
        + eapply IHt2.
          trivial.
        + destruct (k' <? k')%Z eqn:?;
          simpl; [
              Lia.lia
            |
          ].
          destruct (k' >? k')%Z eqn:?;
          simpl; [
              Lia.lia
            | trivial
          ]. 
    (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":2, "finished":0} *)
    induction t.
    (* - try hammer; admit.   
    - try hammer; admit. *)
    (*** MS END {"type": "proof", "proof_type":"hammer", "total":2, "finished":0} *)
    Restart.
  Proof.
    induction t; 
    prep_proof.
    - reflect lookup_insert_emp; 
      check_goal_unsat.
    - reflect lookup_insert_node; 
      check_goal_unsat.
  Admitted.

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
  MetaCoq Quote Definition lookup_insert_neq_emp := (
    (forall (d : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 lookup d x (Node l y v r) =
 ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 bound x (Node l y v r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v l) y v' r)
   (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
(forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
(forall (l : tree V) (k : Z) (v : V) (r : tree V),
 (lt_t k l /\ gt_t k r /\ ordered l /\ ordered r -> ordered (Node l k v r)) /\
 (ordered (Node l k v r) -> lt_t k l /\ gt_t k r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
 ((k' > k)%Z /\ gt_t k l /\ gt_t k r -> gt_t k (Node l k' v r)) /\
 (gt_t k (Node l k' v r) -> (k' > k)%Z /\ gt_t k l /\ gt_t k r)) ->
(forall k : Z, gt_t k Emp) ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
 ((k' < k)%Z /\ lt_t k l /\ lt_t k r -> lt_t k (Node l k' v r)) /\
 (lt_t k (Node l k' v r) -> (k' < k)%Z /\ lt_t k l /\ lt_t k r)) ->
(forall k : Z, lt_t k Emp) ->
forall (d : V) (k k' : Z) (v : V),
k <> k' -> lookup d k' (insert k v Emp) = lookup d k' Emp
).

  MetaCoq Quote Definition lookup_insert_neq_node := (
    forall (t1 : tree V) (k : Z) (v : V) (t2 : tree V),
(forall (d : V) (k0 k' : Z) (v0 : V),
 k0 <> k' -> lookup d k' (insert k0 v0 t1) = lookup d k' t1) ->
(forall (d : V) (k0 k' : Z) (v0 : V),
 k0 <> k' -> lookup d k' (insert k0 v0 t2) = lookup d k' t2) ->
(forall (d : V) (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 lookup d x (Node l y v0 r) =
 ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v0)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 bound x (Node l y v0 r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v0 (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v0 l) y v' r)
   (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
(forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
(forall (l : tree V) (k0 : Z) (v0 : V) (r : tree V),
 (lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r -> ordered (Node l k0 v0 r)) /\
 (ordered (Node l k0 v0 r) -> lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r -> gt_t k0 (Node l k' v0 r)) /\
 (gt_t k0 (Node l k' v0 r) -> (k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r)) ->
(forall k0 : Z, gt_t k0 Emp) ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r -> lt_t k0 (Node l k' v0 r)) /\
 (lt_t k0 (Node l k' v0 r) -> (k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r)) ->
(forall k0 : Z, lt_t k0 Emp) ->
forall (d : V) (k0 k' : Z) (v0 : V),
k0 <> k' -> lookup d k' (insert k0 v0 (Node t1 k v t2)) = lookup d k' (Node t1 k v t2) 
).
  (*** MS END {"type": "configuration", "config_type":"boilerplate"} *)


  (* hammer does not handle this one *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Theorem lookup_insert_neq :
    forall (t: tree V) d k k' v,
      k <> k' -> 
      lookup d k' (insert k v t) = lookup d k' t.
  (*** MS END {"type": "proof_definition"} *)
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
    induction t;
    simpl in *;
    intros.
    - destruct (_ <? _)%Z eqn:?;
      simpl in *; [
          trivial
        |
      ].
      destruct (_ >? _)%Z eqn:?;
      simpl in *; [
          trivial
        | Lia.lia
      ].
    - destruct (_ <? _)%Z eqn:?;
      simpl in *.
      * erewrite IHt1;
        trivial.
      * destruct (_ >? _)%Z eqn:?;
        simpl.
        + erewrite IHt2;
          trivial.
        + assert (k0 = k) by Lia.lia.
          subst.
          destruct (k' <? k)%Z eqn:?; 
          simpl in *; [
              trivial
            | 
          ].
          destruct (k' >? k)%Z eqn:?; 
          simpl in *; [
              trivial
            | Lia.lia
          ].
    (*** MS END {"type": "proof", "proof_type":"manual"} *)
    Restart.
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":2, "finished":0} *)
    induction t. 
    (* - try hammer. admit.
    - try hammer. admit. *)
    (*** MS END {"type": "proof", "proof_type":"hammer", "total":2, "finished":0} *)
    Restart.
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
    induction t; 
    prep_proof.
    - reflect lookup_insert_neq_emp; 
      check_goal_unsat.
    - reflect lookup_insert_neq_node; 
      check_goal_unsat.
    (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
  Admitted.


(** **** Exercise: 3 stars, standard, optional (bound_correct) *)

(** Specify and prove the correctness of [bound]. State and prove
    three theorems, inspired by those we just proved for [lookup]. *)

(* FILL IN HERE *)

(** **** Exercise: 3 stars, standard, optional (bound_default) *)

(** Prove that if [bound] returns [false], then [lookup] returns
    the default value. Proceed by induction on the tree. *)

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
    MetaCoq Quote Definition bound_default_emp := (
      forall (k : Z) (d : V),
(forall (d0 : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 lookup d0 x (Node l y v r) = ite (x <? y)%Z (lookup d0 x l) (ite (x >? y)%Z (lookup d0 x r) v)) ->
(forall (d0 : V) (x : Z), lookup d0 x Emp = d0) ->
(forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 bound x (Node l y v r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
(forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
(forall (l : tree V) (k0 : Z) (v : V) (r : tree V),
 (lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r -> ordered (Node l k0 v r)) /\
 (ordered (Node l k0 v r) -> lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
 ((k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r -> gt_t k0 (Node l k' v r)) /\
 (gt_t k0 (Node l k' v r) -> (k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r)) ->
(forall k0 : Z, gt_t k0 Emp) ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
 ((k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r -> lt_t k0 (Node l k' v r)) /\
 (lt_t k0 (Node l k' v r) -> (k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r)) ->
(forall k0 : Z, lt_t k0 Emp) -> bound k Emp = false -> lookup d k Emp = d
    ).
  
    MetaCoq Quote Definition bound_default_node := (
      
forall (k : Z) (d : V) (t1 : tree V) (k0 : Z) (v : V) (t2 : tree V),
(bound k t1 = false -> lookup d k t1 = d) ->
(bound k t2 = false -> lookup d k t2 = d) ->
(forall (d0 : V) (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 lookup d0 x (Node l y v0 r) = ite (x <? y)%Z (lookup d0 x l) (ite (x >? y)%Z (lookup d0 x r) v0)) ->
(forall (d0 : V) (x : Z), lookup d0 x Emp = d0) ->
(forall (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 bound x (Node l y v0 r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v0 (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v0 l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
(forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
(forall (l : tree V) (k1 : Z) (v0 : V) (r : tree V),
 (lt_t k1 l /\ gt_t k1 r /\ ordered l /\ ordered r -> ordered (Node l k1 v0 r)) /\
 (ordered (Node l k1 v0 r) -> lt_t k1 l /\ gt_t k1 r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k1 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' > k1)%Z /\ gt_t k1 l /\ gt_t k1 r -> gt_t k1 (Node l k' v0 r)) /\
 (gt_t k1 (Node l k' v0 r) -> (k' > k1)%Z /\ gt_t k1 l /\ gt_t k1 r)) ->
(forall k1 : Z, gt_t k1 Emp) ->
(forall (k1 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' < k1)%Z /\ lt_t k1 l /\ lt_t k1 r -> lt_t k1 (Node l k' v0 r)) /\
 (lt_t k1 (Node l k' v0 r) -> (k' < k1)%Z /\ lt_t k1 l /\ lt_t k1 r)) ->
(forall k1 : Z, lt_t k1 Emp) -> bound k (Node t1 k0 v t2) = false -> lookup d k (Node t1 k0 v t2) = d
    ).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

    (* hammer handles this one *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Theorem bound_default :
    forall k d (t: tree V),
      bound k t = false ->
      lookup d k t = d.
  (*** MS END {"type": "proof_definition"} *)
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
    induction t;
    simpl in *;
    intros; 
    trivial.
    destruct (_ <? _)%Z eqn:?;
    simpl in *; [
        intuition eauto
      |
    ].
    destruct (_ >? _)%Z eqn:?;
    simpl in *; [
        intuition eauto
      | congruence
    ].
    (*** MS END {"type": "proof", "proof_type":"manual"} *)
    Restart.
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
    induction t.
    - try hammer.
    - admit. (* - try hammer; admit. *)
    (*** MS END {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
    Restart.
    
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
    induction t; 
    prep_proof. 
    - reflect bound_default_emp; 
      check_goal_unsat.
    - reflect bound_default_node; 
      check_goal_unsat.
    (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
  Admitted.

(** [] *)

(* ################################################################# *)
(** * BSTs vs. Higher-order Functions (Optional) *)

(** The three theorems we just proved for [lookup] should seem
    familiar: we proved equivalent theorems in [Maps] for maps
    defined as higher-order functions. *)

(** Let's prove analogues to these three theorems for search trees.

    Hint: you do not need to unfold the definitions of [empty_tree],
    [insert], or [lookup].  Instead, use [lookup_insert_eq] and
    [lookup_insert_neq]. *)

(** **** Exercise: 2 stars, standard, optional (lookup_insert_shadow) *)


  (*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition lookup_insert_shadow_emp := (
  (forall (d : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 lookup d x (Node l y v r) = ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 bound x (Node l y v r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
(forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
(forall (l : tree V) (k : Z) (v : V) (r : tree V),
 (lt_t k l /\ gt_t k r /\ ordered l /\ ordered r -> ordered (Node l k v r)) /\
 (ordered (Node l k v r) -> lt_t k l /\ gt_t k r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
 ((k' > k)%Z /\ gt_t k l /\ gt_t k r -> gt_t k (Node l k' v r)) /\
 (gt_t k (Node l k' v r) -> (k' > k)%Z /\ gt_t k l /\ gt_t k r)) ->
(forall k : Z, gt_t k Emp) ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
 ((k' < k)%Z /\ lt_t k l /\ lt_t k r -> lt_t k (Node l k' v r)) /\
 (lt_t k (Node l k' v r) -> (k' < k)%Z /\ lt_t k l /\ lt_t k r)) ->
(forall k : Z, lt_t k Emp) ->
forall (v v' d : V) (k k' : Z), lookup d k' (insert k v (insert k v' Emp)) = lookup d k' (insert k v Emp)
).

MetaCoq Quote Definition lookup_insert_shadow_node := (
  
forall (t1 : tree V) (k : Z) (v : V) (t2 : tree V),
(forall (v0 v' d : V) (k0 k' : Z), lookup d k' (insert k0 v0 (insert k0 v' t1)) = lookup d k' (insert k0 v0 t1)) ->
(forall (v0 v' d : V) (k0 k' : Z), lookup d k' (insert k0 v0 (insert k0 v' t2)) = lookup d k' (insert k0 v0 t2)) ->
(forall (d : V) (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 lookup d x (Node l y v0 r) = ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v0)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 bound x (Node l y v0 r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v0 (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v0 l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
(forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
(forall (l : tree V) (k0 : Z) (v0 : V) (r : tree V),
 (lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r -> ordered (Node l k0 v0 r)) /\
 (ordered (Node l k0 v0 r) -> lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r -> gt_t k0 (Node l k' v0 r)) /\
 (gt_t k0 (Node l k' v0 r) -> (k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r)) ->
(forall k0 : Z, gt_t k0 Emp) ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r -> lt_t k0 (Node l k' v0 r)) /\
 (lt_t k0 (Node l k' v0 r) -> (k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r)) ->
(forall k0 : Z, lt_t k0 Emp) ->
forall (v0 v' d : V) (k0 k' : Z),
lookup d k' (insert k0 v0 (insert k0 v' (Node t1 k v t2))) = lookup d k' (insert k0 v0 (Node t1 k v t2))
).
  (*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

  (* hammer does not handle this one *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma lookup_insert_shadow :
    forall (t: tree V) v v' d k k',
      lookup d k' (insert k v (insert k v' t)) = lookup d k' (insert k v t).
  (*** MS END {"type": "proof_definition"} *)
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
    induction t;
    simpl in *;
    intros.
    - assert ((k <? k)%Z = false) by Lia.lia. 
      erewrite H;
      simpl.
      assert ((k >? k)%Z = false) by Lia.lia. 
      erewrite H0;
      simpl.
      trivial.
    - destruct (_ <? _)%Z eqn:?;
      simpl in *.
      + erewrite Heqb;
        simpl.
        f_equal.
        eapply IHt1.
      + destruct (_ >? _)%Z eqn:?;
        simpl in *.
        * erewrite Heqb.
          erewrite Heqb0.
          simpl.
          f_equal.
          f_equal.
          eapply IHt2.
        * assert ((k0 <? k0)%Z = false) by Lia.lia.
          assert ((k0 >? k0)%Z = false) by Lia.lia.
          erewrite H.
          erewrite H0.
          simpl.
          f_equal.
    (*** MS END {"type": "proof", "proof_type":"manual"} *)
    Restart.   
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":2, "finished":0} *)
    induction t.
    - admit. (* try hammer; admit.*)
    - admit. (* try hammer; admit. *)
    (*** MS END {"type": "proof", "proof_type":"hammer", "total":2, "finished":0} *)
    Restart.
  Proof.
(*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
    induction t; 
    prep_proof.
    - reflect lookup_insert_shadow_emp; 
      check_goal_unsat.
    - reflect lookup_insert_shadow_node; 
      check_goal_unsat.
(*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
  Admitted.

  (*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
  MetaCoq Quote Definition lookup_insert_same_emp := (
    forall (k k' : Z) (d : V),
    (forall (d0 : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
     lookup d0 x (Node l y v r) = ite (x <? y)%Z (lookup d0 x l) (ite (x >? y)%Z (lookup d0 x r) v)) ->
    (forall (d0 : V) (x : Z), lookup d0 x Emp = d0) ->
    (forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
     bound x (Node l y v r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
    (forall x : Z, bound x Emp = false) ->
    (forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
     insert x v (Node l y v' r) =
     ite (x <? y)%Z (Node (insert x v l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
    (forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
    (forall (l : tree V) (k0 : Z) (v : V) (r : tree V),
     (lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r -> ordered (Node l k0 v r)) /\
     (ordered (Node l k0 v r) -> lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r)) ->
    ordered Emp ->
    (forall (k0 : Z) (l : tree V) (k'0 : Z) (v : V) (r : tree V),
     ((k'0 > k0)%Z /\ gt_t k0 l /\ gt_t k0 r -> gt_t k0 (Node l k'0 v r)) /\
     (gt_t k0 (Node l k'0 v r) -> (k'0 > k0)%Z /\ gt_t k0 l /\ gt_t k0 r)) ->
    (forall k0 : Z, gt_t k0 Emp) ->
    (forall (k0 : Z) (l : tree V) (k'0 : Z) (v : V) (r : tree V),
     ((k'0 < k0)%Z /\ lt_t k0 l /\ lt_t k0 r -> lt_t k0 (Node l k'0 v r)) /\
     (lt_t k0 (Node l k'0 v r) -> (k'0 < k0)%Z /\ lt_t k0 l /\ lt_t k0 r)) ->
    (forall k0 : Z, lt_t k0 Emp) -> lookup d k' (insert k (lookup d k Emp) Emp) = lookup d k' Emp    
  ).
  
  MetaCoq Quote Definition lookup_insert_same_node := (
    
forall (k k' : Z) (d : V) (t1 : tree V) (k0 : Z) (v : V) (t2 : tree V),
lookup d k' (insert k (lookup d k t1) t1) = lookup d k' t1 ->
lookup d k' (insert k (lookup d k t2) t2) = lookup d k' t2 ->
(forall (d0 : V) (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 lookup d0 x (Node l y v0 r) = ite (x <? y)%Z (lookup d0 x l) (ite (x >? y)%Z (lookup d0 x r) v0)) ->
(forall (d0 : V) (x : Z), lookup d0 x Emp = d0) ->
(forall (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 bound x (Node l y v0 r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v0 (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v0 l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
(forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
(forall (l : tree V) (k1 : Z) (v0 : V) (r : tree V),
 (lt_t k1 l /\ gt_t k1 r /\ ordered l /\ ordered r -> ordered (Node l k1 v0 r)) /\
 (ordered (Node l k1 v0 r) -> lt_t k1 l /\ gt_t k1 r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k1 : Z) (l : tree V) (k'0 : Z) (v0 : V) (r : tree V),
 ((k'0 > k1)%Z /\ gt_t k1 l /\ gt_t k1 r -> gt_t k1 (Node l k'0 v0 r)) /\
 (gt_t k1 (Node l k'0 v0 r) -> (k'0 > k1)%Z /\ gt_t k1 l /\ gt_t k1 r)) ->
(forall k1 : Z, gt_t k1 Emp) ->
(forall (k1 : Z) (l : tree V) (k'0 : Z) (v0 : V) (r : tree V),
 ((k'0 < k1)%Z /\ lt_t k1 l /\ lt_t k1 r -> lt_t k1 (Node l k'0 v0 r)) /\
 (lt_t k1 (Node l k'0 v0 r) -> (k'0 < k1)%Z /\ lt_t k1 l /\ lt_t k1 r)) ->
(forall k1 : Z, lt_t k1 Emp) ->
lookup d k' (insert k (lookup d k (Node t1 k0 v t2)) (Node t1 k0 v t2)) = lookup d k' (Node t1 k0 v t2)
  ).
  (*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

  (** **** Exercise: 2 stars, standard, optional (lookup_insert_same) *)

  (* hammer does not handle this one *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma lookup_insert_same :
    forall k k' d (t: tree V),
      lookup d k' (insert k (lookup d k t) t) = lookup d k' t.
  (*** MS END {"type": "proof_definition"} *)
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
    induction t; 
    simpl in *;
    intros.
    - destruct (_ <? _)%Z eqn:?;
      simpl in *;
      trivial.
      destruct (_ >? _)%Z eqn:?;
      simpl in *;
      trivial.
    - destruct (_ <? _)%Z eqn:?;
      simpl in *;
      trivial.
      + f_equal.
        eauto.
      + destruct (_ >? _)%Z eqn:?;
        simpl in *;
        trivial;
        destruct (_ <? _)%Z eqn:?;
        simpl.
        * f_equal.
          f_equal.
          eauto.
        * f_equal;
          f_equal;
          eauto.
        * congruence.
        * f_equal; [
            Lia.lia
            | f_equal
          ].
          Lia.lia.
    (*** MS END {"type": "proof", "proof_type":"manual"} *)
    Restart.
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":2, "finished":0} *)
    induction t.
    - admit.
    - admit.
    (*** MS END {"type": "proof", "proof_type":"hammer", "total":2, "finished":0} *)
    Restart.
  Proof. 
    (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
    induction t; 
    prep_proof.
    - reflect lookup_insert_same_emp; 
      check_goal_unsat.
    - reflect lookup_insert_same_node; 
      check_goal_unsat.
    (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
  Admitted.


  (*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
  MetaCoq Quote Definition lookup_insert_permute_emp := (
    forall (v1 v2 d : V) (k1 k2 k' : Z),
(forall (d0 : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 lookup d0 x (Node l y v r) = ite (x <? y)%Z (lookup d0 x l) (ite (x >? y)%Z (lookup d0 x r) v)) ->
(forall (d0 : V) (x : Z), lookup d0 x Emp = d0) ->
(forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 bound x (Node l y v r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
(forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
(forall (l : tree V) (k : Z) (v : V) (r : tree V),
 (lt_t k l /\ gt_t k r /\ ordered l /\ ordered r -> ordered (Node l k v r)) /\
 (ordered (Node l k v r) -> lt_t k l /\ gt_t k r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k : Z) (l : tree V) (k'0 : Z) (v : V) (r : tree V),
 ((k'0 > k)%Z /\ gt_t k l /\ gt_t k r -> gt_t k (Node l k'0 v r)) /\
 (gt_t k (Node l k'0 v r) -> (k'0 > k)%Z /\ gt_t k l /\ gt_t k r)) ->
(forall k : Z, gt_t k Emp) ->
(forall (k : Z) (l : tree V) (k'0 : Z) (v : V) (r : tree V),
 ((k'0 < k)%Z /\ lt_t k l /\ lt_t k r -> lt_t k (Node l k'0 v r)) /\
 (lt_t k (Node l k'0 v r) -> (k'0 < k)%Z /\ lt_t k l /\ lt_t k r)) ->
(forall k : Z, lt_t k Emp) ->
k1 <> k2 -> lookup d k' (insert k1 v1 (insert k2 v2 Emp)) = lookup d k' (insert k2 v2 (insert k1 v1 Emp))
).
  
  MetaCoq Quote Definition lookup_insert_permute_node := (
    
forall (v1 v2 d : V) (k1 k2 k' : Z) (t1 : tree V) (k : Z) (v : V) (t2 : tree V),
(k1 <> k2 -> lookup d k' (insert k1 v1 (insert k2 v2 t1)) = lookup d k' (insert k2 v2 (insert k1 v1 t1))) ->
(k1 <> k2 -> lookup d k' (insert k1 v1 (insert k2 v2 t2)) = lookup d k' (insert k2 v2 (insert k1 v1 t2))) ->
(forall (d0 : V) (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 lookup d0 x (Node l y v0 r) = ite (x <? y)%Z (lookup d0 x l) (ite (x >? y)%Z (lookup d0 x r) v0)) ->
(forall (d0 : V) (x : Z), lookup d0 x Emp = d0) ->
(forall (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 bound x (Node l y v0 r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v0 (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v0 l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
(forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
(forall (l : tree V) (k0 : Z) (v0 : V) (r : tree V),
 (lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r -> ordered (Node l k0 v0 r)) /\
 (ordered (Node l k0 v0 r) -> lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k0 : Z) (l : tree V) (k'0 : Z) (v0 : V) (r : tree V),
 ((k'0 > k0)%Z /\ gt_t k0 l /\ gt_t k0 r -> gt_t k0 (Node l k'0 v0 r)) /\
 (gt_t k0 (Node l k'0 v0 r) -> (k'0 > k0)%Z /\ gt_t k0 l /\ gt_t k0 r)) ->
(forall k0 : Z, gt_t k0 Emp) ->
(forall (k0 : Z) (l : tree V) (k'0 : Z) (v0 : V) (r : tree V),
 ((k'0 < k0)%Z /\ lt_t k0 l /\ lt_t k0 r -> lt_t k0 (Node l k'0 v0 r)) /\
 (lt_t k0 (Node l k'0 v0 r) -> (k'0 < k0)%Z /\ lt_t k0 l /\ lt_t k0 r)) ->
(forall k0 : Z, lt_t k0 Emp) ->
k1 <> k2 ->
lookup d k' (insert k1 v1 (insert k2 v2 (Node t1 k v t2))) = lookup d k' (insert k2 v2 (insert k1 v1 (Node t1 k v t2)))
  ).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

  (** **** Exercise: 2 stars, standard, optional (lookup_insert_permute) *)

  (* hammer does not handle this one *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma lookup_insert_permute :
    forall v1 v2 d k1 k2 k' (t: tree V),
      k1 <> k2 ->
      lookup d k' (insert k1 v1 (insert k2 v2 t))
      = lookup d k' (insert k2 v2 (insert k1 v1 t)).
  (*** MS END {"type": "proof_definition"} *)
  Proof. 
    (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
    induction t;
    simpl in *;
    intros.
    - destruct (_ <? _)%Z eqn:?;  
      simpl.
      * assert ((k2 <? k1)%Z = false) by Lia.lia.
        assert ((k2 >? k1)%Z = true) by Lia.lia.
        erewrite H0.
        erewrite H1.
        simpl.
        destruct (k' <? k2)%Z eqn:?;
        simpl; [
          trivial
          | 
        ].
        destruct (k' <? k1)%Z eqn:?;
        assert ((k' >? k1)%Z = true) by Lia.lia;
        erewrite H2;
        simpl.
        + destruct (k' >? k2)%Z eqn:?;
          simpl; [
              trivial
            | Lia.lia
          ].
        + destruct (k' >? k2)%Z eqn:?;
          simpl;
          trivial.
      * assert ((k2 <? k1)%Z = true) by Lia.lia.
        assert ((k2 >? k1)%Z = false) by Lia.lia.
        erewrite H0.
        erewrite H1.
        simpl.
        destruct (k' <? k1)%Z eqn:?;
        simpl; 
        assert ((k1 >? k2)%Z = true) by Lia.lia;
        erewrite H2;
        simpl.
        + f_equal.
          f_equal.
          erewrite Heqb0;
          trivial.
        + destruct (k' <? k2)%Z eqn:?;
          try Lia.lia;
          assert ((k' >? k2)%Z = true) by Lia.lia;
          erewrite H3;
          erewrite Heqb0;
          simpl;
          f_equal.
    - destruct (k2 <? k)%Z eqn:?;
      destruct (k2 >? k)%Z eqn:?;
      destruct (k1 <? k)%Z eqn:?;
      destruct (k1 >? k)%Z eqn:?;
      simpl;
      try Lia.lia.
      * erewrite Heqb1.
        erewrite Heqb.
        simpl.
        f_equal;  
        eauto.
      * erewrite Heqb1.
        erewrite Heqb0.
        erewrite Heqb2.
        erewrite Heqb.
        simpl.
        f_equal.
      * erewrite Heqb1.
        erewrite Heqb2.
        simpl.
        destruct (k2 <? k1)%Z eqn:?;
        simpl;
        trivial.
        assert ((k2 >? k1)%Z = true) by Lia.lia.
        erewrite H0.
        simpl.
        f_equal.
        + eapply lookup_insert_neq;
          Lia.lia.
        + f_equal.
          erewrite lookup_insert_neq;
          trivial.
          Lia.lia.
      * erewrite Heqb1;
        erewrite Heqb;
        erewrite Heqb0;
        erewrite Heqb2;
        simpl.
        f_equal.
      * erewrite Heqb1;
        erewrite Heqb;
        erewrite Heqb0;
        erewrite Heqb2;
        simpl.
        f_equal.
        f_equal.
        eapply IHt2.
        trivial.
      * erewrite Heqb1;
        erewrite Heqb2;
        simpl;
        destruct (k2 <? k1)%Z eqn:?;
        simpl;
        try Lia.lia.
        assert ((k2 >? k1)%Z = true) by Lia.lia.
        erewrite H0.
        simpl.
        f_equal.
      * erewrite Heqb;
        erewrite Heqb0;
        simpl.
        destruct (k1 <? k2)%Z eqn:?;
        simpl; [
            f_equal
          |
        ].
        assert ((k1 >? k2)%Z = true) by Lia.lia.
        erewrite H0.
        simpl.
        f_equal;
        try Lia.lia.
      * erewrite Heqb;
        erewrite Heqb0;
        simpl.
        destruct (k1 <? k2)%Z eqn:?;
        simpl; [
            Lia.lia
          |
        ].
        assert ((k1 >? k2)%Z = true) by Lia.lia.
        erewrite H0.
        simpl.
        f_equal.
    (*** MS END {"type": "proof", "proof_type":"manual"} *)
    Restart.
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":2, "finished":0} *)
    induction t.
    - admit. (* hammer. *)
    - admit. (* hammer. *)
    (*** MS END {"type": "proof", "proof_type":"hammer", "total":2, "finished":0} *)
  Restart.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
    induction t; 
    prep_proof.
    - reflect lookup_insert_permute_emp; 
      check_goal_unsat.
    - reflect lookup_insert_permute_node; 
      check_goal_unsat.
  (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
  Admitted.

(** Our ability to prove these lemmas without reference to the
    underlying tree implementation demonstrates they hold for any map
    implementation that satisfies the three basic equations. *)

(** Each of these lemmas just proved was phrased as an equality
    between the results of looking up an arbitrary key [k'] in two
    maps.  But the lemmas for the function-based maps were phrased as
    direct equalities between the maps themselves.

    Could we state the tree lemmas with direct equalities?  For
    [insert_shadow], the answer is yes: *)

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
    MetaCoq Quote Definition insert_shadow_equality_emp := (
      (forall (d : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 lookup d x (Node l y v r) = ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 bound x (Node l y v r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
(forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
(forall (l : tree V) (k : Z) (v : V) (r : tree V),
 (lt_t k l /\ gt_t k r /\ ordered l /\ ordered r -> ordered (Node l k v r)) /\
 (ordered (Node l k v r) -> lt_t k l /\ gt_t k r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
 ((k' > k)%Z /\ gt_t k l /\ gt_t k r -> gt_t k (Node l k' v r)) /\
 (gt_t k (Node l k' v r) -> (k' > k)%Z /\ gt_t k l /\ gt_t k r)) ->
(forall k : Z, gt_t k Emp) ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
 ((k' < k)%Z /\ lt_t k l /\ lt_t k r -> lt_t k (Node l k' v r)) /\
 (lt_t k (Node l k' v r) -> (k' < k)%Z /\ lt_t k l /\ lt_t k r)) ->
(forall k : Z, lt_t k Emp) -> forall (k : Z) (v v' : V), insert k v (insert k v' Emp) = insert k v Emp
  ).
    
    MetaCoq Quote Definition insert_shadow_equality_node := (
      
forall (t1 : tree V) (k : Z) (v : V) (t2 : tree V),
(forall (k0 : Z) (v0 v' : V), insert k0 v0 (insert k0 v' t1) = insert k0 v0 t1) ->
(forall (k0 : Z) (v0 v' : V), insert k0 v0 (insert k0 v' t2) = insert k0 v0 t2) ->
(forall (d : V) (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 lookup d x (Node l y v0 r) = ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v0)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 bound x (Node l y v0 r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v0 (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v0 l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
(forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
(forall (l : tree V) (k0 : Z) (v0 : V) (r : tree V),
 (lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r -> ordered (Node l k0 v0 r)) /\
 (ordered (Node l k0 v0 r) -> lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r -> gt_t k0 (Node l k' v0 r)) /\
 (gt_t k0 (Node l k' v0 r) -> (k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r)) ->
(forall k0 : Z, gt_t k0 Emp) ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r -> lt_t k0 (Node l k' v0 r)) /\
 (lt_t k0 (Node l k' v0 r) -> (k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r)) ->
(forall k0 : Z, lt_t k0 Emp) ->
forall (k0 : Z) (v0 v' : V), insert k0 v0 (insert k0 v' (Node t1 k v t2)) = insert k0 v0 (Node t1 k v t2)
    ).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)


  (* hammer does not handle this one *)
  (*** MS BEGIN {"type": "proof_definition"} *)
  Lemma insert_shadow_equality : 
    forall (t: tree V) k v v',
      insert k v (insert k v' t) = insert k v t.
  (*** MS END {"type": "proof_definition"} *)
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
    induction t;
    simpl in *;
    intros.
    - assert ((k <? k)%Z = false) by Lia.lia;
      assert ((k >? k)%Z = false) by Lia.lia;
      erewrite H;
      erewrite H0;
      simpl.
      trivial.
    - destruct (_ <? _)%Z eqn:?;
      simpl.
      * erewrite Heqb.
        simpl.
        f_equal.
        eapply IHt1.
      * destruct (k0 >? k)%Z eqn:?;
        simpl.
        + erewrite Heqb.
          erewrite Heqb0.
          simpl.
          f_equal.
          eapply IHt2.
        + assert ((k0 <? k0)%Z = false) by Lia.lia.
          erewrite H;
          simpl.
          assert ((k0 >? k0)%Z = false) by Lia.lia;
          erewrite H0;
          simpl.
          trivial.
    (*** MS END {"type": "proof", "proof_type":"manual"} *)
    Restart.
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":2, "finished":0} *)
    induction t.
    - admit. (* hammer. *)
    - admit. (* hammer. *)
    (*** MS END {"type": "proof", "proof_type":"hammer", "total":2, "finished":0} *)
    Restart.
  Proof.
    (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
    induction t; 
    prep_proof.
    - reflect insert_shadow_equality_emp; 
      check_goal_unsat.
    - reflect insert_shadow_equality_node; 
      check_goal_unsat.
    (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
  Admitted.

(** But the other two direct equalities on BSTs do not necessarily
    hold. *)

(** **** Exercise: 3 stars, standard, optional (direct_equalities_break) *)

(** Prove that the other equalities do not hold.  Hint: find a counterexample
    first on paper, then use the [exists] tactic to instantiate the theorem
    on your counterexample.  The simpler your counterexample, the simpler
    the rest of the proof will be. *)

(* Lemma insert_same_equality_breaks :
  exists (V : Type) (d : V) (t : tree V) (k : key),
      insert k (lookup d k t) t <> t.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma insert_permute_equality_breaks :
  exists (V : Type) (v1 v2 : V) (k1 k2 : key) (t : tree V),
    k1 <> k2 /\ insert k1 v1 (insert k2 v2 t) <> insert k2 v2 (insert k1 v1 t).
Proof.
  (* FILL IN HERE *) Admitted. *)

(** [] *)

(** some custom stuff, about balance and that insert preserves the balance of the tree **)

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition insert_left_lt_emp := (
  
(forall (d : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
lookup d x (Node l y v r) = ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
bound x (Node l y v r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
insert x v (Node l y v' r) =
ite (x <? y)%Z (Node (insert x v l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
(forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
(forall (l : tree V) (k : Z) (v : V) (r : tree V),
(lt_t k l /\ gt_t k r /\ ordered l /\ ordered r -> ordered (Node l k v r)) /\
(ordered (Node l k v r) -> lt_t k l /\ gt_t k r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
((k' > k)%Z /\ gt_t k l /\ gt_t k r -> gt_t k (Node l k' v r)) /\
(gt_t k (Node l k' v r) -> (k' > k)%Z /\ gt_t k l /\ gt_t k r)) ->
(forall k : Z, gt_t k Emp) ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
((k' < k)%Z /\ lt_t k l /\ lt_t k r -> lt_t k (Node l k' v r)) /\
(lt_t k (Node l k' v r) -> (k' < k)%Z /\ lt_t k l /\ lt_t k r)) ->
(forall k : Z, lt_t k Emp) -> forall (k k' : Z) (v : V), (k < k')%Z -> lt_t k' Emp -> lt_t k' (insert k v Emp)
).

MetaCoq Quote Definition insert_left_lt_node := (
  forall (l1 : tree V) (k : Z) (v : V) (l2 : tree V),
(forall (k0 k' : Z) (v0 : V), (k0 < k')%Z -> lt_t k' l1 -> lt_t k' (insert k0 v0 l1)) ->
(forall (k0 k' : Z) (v0 : V), (k0 < k')%Z -> lt_t k' l2 -> lt_t k' (insert k0 v0 l2)) ->
(forall (d : V) (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 lookup d x (Node l y v0 r) = ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v0)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 bound x (Node l y v0 r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v0 (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v0 l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
(forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
(forall (l : tree V) (k0 : Z) (v0 : V) (r : tree V),
 (lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r -> ordered (Node l k0 v0 r)) /\
 (ordered (Node l k0 v0 r) -> lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r -> gt_t k0 (Node l k' v0 r)) /\
 (gt_t k0 (Node l k' v0 r) -> (k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r)) ->
(forall k0 : Z, gt_t k0 Emp) ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r -> lt_t k0 (Node l k' v0 r)) /\
 (lt_t k0 (Node l k' v0 r) -> (k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r)) ->
(forall k0 : Z, lt_t k0 Emp) ->
forall (k0 k' : Z) (v0 : V), (k0 < k')%Z -> lt_t k' (Node l1 k v l2) -> lt_t k' (insert k0 v0 (Node l1 k v l2))
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(* unfortunately we can't handle the recursive case *)
SetSMTSolver "cvc5".
(*** MS BEGIN {"type": "proof_definition"} *)
Lemma insert_left_lt : 
  forall (l: tree V) k k' v, 
    (k < k')%Z -> 
    lt_t k' l -> 
    lt_t k' (insert k v l).
(*** MS END {"type": "proof_definition"} *)
Proof. 
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  induction l;
  intros; 
  simpl in *.
  - intuition.
  - destruct (k0 <? k)%Z eqn:?;
    simpl in *; [
        intuition 
      | 
    ].
    destruct (k0 >? k)%Z eqn:?;
    simpl in *; 
    intuition.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
  induction l.
  - hammer.
  - admit. (* hammer. *)
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
  induction l;
  prep_proof.
  - reflect insert_left_lt_emp; 
    check_goal_unsat.
  - reflect insert_left_lt_node;
    check_goal_unsat.
(*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
Admitted.

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition insert_right_lt_emp := (
  
(forall (d : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
lookup d x (Node l y v r) = ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
bound x (Node l y v r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
insert x v (Node l y v' r) =
ite (x <? y)%Z (Node (insert x v l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
(forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
(forall (l : tree V) (k : Z) (v : V) (r : tree V),
(lt_t k l /\ gt_t k r /\ ordered l /\ ordered r -> ordered (Node l k v r)) /\
(ordered (Node l k v r) -> lt_t k l /\ gt_t k r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
((k' > k)%Z /\ gt_t k l /\ gt_t k r -> gt_t k (Node l k' v r)) /\
(gt_t k (Node l k' v r) -> (k' > k)%Z /\ gt_t k l /\ gt_t k r)) ->
(forall k : Z, gt_t k Emp) ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
((k' < k)%Z /\ lt_t k l /\ lt_t k r -> lt_t k (Node l k' v r)) /\
(lt_t k (Node l k' v r) -> (k' < k)%Z /\ lt_t k l /\ lt_t k r)) ->
(forall k : Z, lt_t k Emp) -> forall (k k' : Z) (v : V), (k' < k)%Z -> gt_t k' Emp -> gt_t k' (insert k v Emp)
).

MetaCoq Quote Definition insert_right_lt_node := (
  
forall (r1 : tree V) (k : Z) (v : V) (r2 : tree V),
(forall (k0 k' : Z) (v0 : V), (k' < k0)%Z -> gt_t k' r1 -> gt_t k' (insert k0 v0 r1)) ->
(forall (k0 k' : Z) (v0 : V), (k' < k0)%Z -> gt_t k' r2 -> gt_t k' (insert k0 v0 r2)) ->
(forall (d : V) (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 lookup d x (Node l y v0 r) = ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v0)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 bound x (Node l y v0 r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v0 (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v0 l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
(forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
(forall (l : tree V) (k0 : Z) (v0 : V) (r : tree V),
 (lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r -> ordered (Node l k0 v0 r)) /\
 (ordered (Node l k0 v0 r) -> lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r -> gt_t k0 (Node l k' v0 r)) /\
 (gt_t k0 (Node l k' v0 r) -> (k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r)) ->
(forall k0 : Z, gt_t k0 Emp) ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r -> lt_t k0 (Node l k' v0 r)) /\
 (lt_t k0 (Node l k' v0 r) -> (k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r)) ->
(forall k0 : Z, lt_t k0 Emp) ->
forall (k0 k' : Z) (v0 : V), (k' < k0)%Z -> gt_t k' (Node r1 k v r2) -> gt_t k' (insert k0 v0 (Node r1 k v r2))
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(*** MS BEGIN {"type": "proof_definition"} *)
Lemma insert_right_lt : 
  forall (r: tree V) k k' v, 
    (k' < k)%Z -> 
    gt_t k' r -> 
    gt_t k' (insert k v r).
(*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  induction r;
  intros; 
  simpl in *.
  - intuition.
  - destruct (k0 <? k)%Z eqn:?;
    simpl in *; [
        intuition 
      | 
    ].
    destruct (k0 >? k)%Z eqn:?;
    simpl in *; 
    intuition.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":2, "finished":0} *)
  induction r.
  - admit. (* hammer. *)
  - admit. (* hammer. *)
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":2, "finished":0} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
  induction r;
  prep_proof.
  - reflect insert_right_lt_emp; 
    check_goal_unsat.
  - reflect insert_right_lt_node; 
    check_goal_unsat.
  (*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
Admitted.
(*** MS BEGIN {"type": "configuration", "config_type":"tactics"} *)
Ltac prep_proof' := Utils.pose_all (tt, insert_left_lt, insert_right_lt); 
  prep_proof.
(*** MS END {"type": "configuration", "config_type":"tactics"} *)

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition insert_ordered_left_emp := (
  
(forall (r : tree V) (k k' : Z) (v : V), (k' < k)%Z -> gt_t k' r -> gt_t k' (insert k v r)) ->
(forall (l : tree V) (k k' : Z) (v : V), (k < k')%Z -> lt_t k' l -> lt_t k' (insert k v l)) ->
(forall (d : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 lookup d x (Node l y v r) = ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 bound x (Node l y v r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
(forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
(forall (l : tree V) (k : Z) (v : V) (r : tree V),
 (lt_t k l /\ gt_t k r /\ ordered l /\ ordered r -> ordered (Node l k v r)) /\
 (ordered (Node l k v r) -> lt_t k l /\ gt_t k r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
 ((k' > k)%Z /\ gt_t k l /\ gt_t k r -> gt_t k (Node l k' v r)) /\
 (gt_t k (Node l k' v r) -> (k' > k)%Z /\ gt_t k l /\ gt_t k r)) ->
(forall k : Z, gt_t k Emp) ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
 ((k' < k)%Z /\ lt_t k l /\ lt_t k r -> lt_t k (Node l k' v r)) /\
 (lt_t k (Node l k' v r) -> (k' < k)%Z /\ lt_t k l /\ lt_t k r)) ->
(forall k : Z, lt_t k Emp) ->
forall (k k' : Z) (v : V), (k < k')%Z -> lt_t k' Emp -> ordered Emp -> ordered (insert k v Emp)
).

MetaCoq Quote Definition insert_ordered_left_node := (
  forall (l1 : tree V) (k : Z) (v : V) (l2 : tree V),
(forall (k0 k' : Z) (v0 : V), (k0 < k')%Z -> lt_t k' l1 -> ordered l1 -> ordered (insert k0 v0 l1)) ->
(forall (k0 k' : Z) (v0 : V), (k0 < k')%Z -> lt_t k' l2 -> ordered l2 -> ordered (insert k0 v0 l2)) ->
(forall (r : tree V) (k0 k' : Z) (v0 : V), (k' < k0)%Z -> gt_t k' r -> gt_t k' (insert k0 v0 r)) ->
(forall (l : tree V) (k0 k' : Z) (v0 : V), (k0 < k')%Z -> lt_t k' l -> lt_t k' (insert k0 v0 l)) ->
(forall (d : V) (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 lookup d x (Node l y v0 r) = ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v0)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 bound x (Node l y v0 r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v0 (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v0 l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
(forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
(forall (l : tree V) (k0 : Z) (v0 : V) (r : tree V),
 (lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r -> ordered (Node l k0 v0 r)) /\
 (ordered (Node l k0 v0 r) -> lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r -> gt_t k0 (Node l k' v0 r)) /\
 (gt_t k0 (Node l k' v0 r) -> (k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r)) ->
(forall k0 : Z, gt_t k0 Emp) ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r -> lt_t k0 (Node l k' v0 r)) /\
 (lt_t k0 (Node l k' v0 r) -> (k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r)) ->
(forall k0 : Z, lt_t k0 Emp) ->
forall (k0 k' : Z) (v0 : V),
(k0 < k')%Z -> lt_t k' (Node l1 k v l2) -> ordered (Node l1 k v l2) -> ordered (insert k0 v0 (Node l1 k v l2))
).

(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(*** MS BEGIN {"type": "proof_definition"} *)
Lemma insert_ordered_left :
  forall (l: tree V) k k' v, 
    (k < k')%Z -> 
    lt_t k' l -> 
    ordered l ->
    ordered (insert k v l).
(*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  induction l;
  intros;
  simpl in *.
  - intuition.
  - destruct (k0 <? k)%Z eqn:?;
    simpl in *.
    * intuition.
      eapply insert_left_lt;
      eauto.
      Lia.lia.
    * destruct (k0 >? k)%Z eqn:?;
      simpl in *; 
      intuition.
      + eapply insert_right_lt;
        intuition.
      + assert (k0 = k) by Lia.lia.
        subst.
        trivial.
      + assert (k0 = k) by Lia.lia.
        subst.
        trivial.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
  induction l.
  - hammer.
  - admit. (* hammer. *)
  (*** MS END {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
  induction l;
  prep_proof'.
  - reflect insert_ordered_left_emp; 
    check_goal_unsat.
  - reflect insert_ordered_left_node; 
    check_goal_unsat. 
(*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
Admitted.

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition insert_ordered_right_emp := (
  (forall (r : tree V) (k k' : Z) (v : V), (k' < k)%Z -> gt_t k' r -> gt_t k' (insert k v r)) ->
(forall (l : tree V) (k k' : Z) (v : V), (k < k')%Z -> lt_t k' l -> lt_t k' (insert k v l)) ->
(forall (d : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 lookup d x (Node l y v r) = ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 bound x (Node l y v r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
(forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
(forall (l : tree V) (k : Z) (v : V) (r : tree V),
 (lt_t k l /\ gt_t k r /\ ordered l /\ ordered r -> ordered (Node l k v r)) /\
 (ordered (Node l k v r) -> lt_t k l /\ gt_t k r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
 ((k' > k)%Z /\ gt_t k l /\ gt_t k r -> gt_t k (Node l k' v r)) /\
 (gt_t k (Node l k' v r) -> (k' > k)%Z /\ gt_t k l /\ gt_t k r)) ->
(forall k : Z, gt_t k Emp) ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
 ((k' < k)%Z /\ lt_t k l /\ lt_t k r -> lt_t k (Node l k' v r)) /\
 (lt_t k (Node l k' v r) -> (k' < k)%Z /\ lt_t k l /\ lt_t k r)) ->
(forall k : Z, lt_t k Emp) ->
forall (k k' : Z) (v : V), (k > k')%Z -> gt_t k' Emp -> ordered Emp -> ordered (insert k v Emp)
).

MetaCoq Quote Definition insert_ordered_right_node := (
  forall (r1 : tree V) (k : Z) (v : V) (r2 : tree V),
(forall (k0 k' : Z) (v0 : V), (k0 > k')%Z -> gt_t k' r1 -> ordered r1 -> ordered (insert k0 v0 r1)) ->
(forall (k0 k' : Z) (v0 : V), (k0 > k')%Z -> gt_t k' r2 -> ordered r2 -> ordered (insert k0 v0 r2)) ->
(forall (r : tree V) (k0 k' : Z) (v0 : V), (k' < k0)%Z -> gt_t k' r -> gt_t k' (insert k0 v0 r)) ->
(forall (l : tree V) (k0 k' : Z) (v0 : V), (k0 < k')%Z -> lt_t k' l -> lt_t k' (insert k0 v0 l)) ->
(forall (d : V) (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 lookup d x (Node l y v0 r) = ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v0)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 bound x (Node l y v0 r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v0 (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v0 l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
(forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
(forall (l : tree V) (k0 : Z) (v0 : V) (r : tree V),
 (lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r -> ordered (Node l k0 v0 r)) /\
 (ordered (Node l k0 v0 r) -> lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r -> gt_t k0 (Node l k' v0 r)) /\
 (gt_t k0 (Node l k' v0 r) -> (k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r)) ->
(forall k0 : Z, gt_t k0 Emp) ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r -> lt_t k0 (Node l k' v0 r)) /\
 (lt_t k0 (Node l k' v0 r) -> (k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r)) ->
(forall k0 : Z, lt_t k0 Emp) ->
forall (k0 k' : Z) (v0 : V),
(k0 > k')%Z -> gt_t k' (Node r1 k v r2) -> ordered (Node r1 k v r2) -> ordered (insert k0 v0 (Node r1 k v r2))
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(*** MS BEGIN {"type": "proof_definition"} *)
Lemma insert_ordered_right :
forall (r: tree V) k k' v, 
  (k > k')%Z -> 
  gt_t k' r -> 
  ordered r ->
  ordered (insert k v r).
(*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  induction r;
  intros;
  simpl in *.
  - intuition.
  - destruct (k0 <? k)%Z eqn:?;
    simpl in *.
    * intuition.
      eapply insert_left_lt;
      eauto.
      Lia.lia.
    * destruct (k0 >? k)%Z eqn:?;
      simpl in *; 
      intuition.
      + eapply insert_right_lt;
        intuition.
      + assert (k0 = k) by Lia.lia.
        subst.
        trivial.
      + assert (k0 = k) by Lia.lia.
        subst.
        trivial.
  Restart.
  (*** MS END {"type": "proof", "proof_type":"manual"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
  induction r.
  - hammer.
  - admit. (* hammer. *)
(*** MS END {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
  induction r;
  prep_proof'.
  - reflect insert_ordered_right_emp; 
    check_goal_unsat.
  - reflect insert_ordered_right_node; 
    check_goal_unsat.
(*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
Admitted.
  
(*** MS BEGIN {"type": "configuration", "config_type":"tactics"} *)
Ltac prep_proof'' := Utils.pose_all (tt, insert_ordered_left, insert_ordered_right);
  prep_proof'.
(*** MS END {"type": "configuration", "config_type":"tactics"} *)

(*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
MetaCoq Quote Definition insert_ordered_emp := (
  
(forall (r : tree V) (k k' : Z) (v : V), (k > k')%Z -> gt_t k' r -> ordered r -> ordered (insert k v r)) ->
(forall (l : tree V) (k k' : Z) (v : V), (k < k')%Z -> lt_t k' l -> ordered l -> ordered (insert k v l)) ->
(forall (r : tree V) (k k' : Z) (v : V), (k' < k)%Z -> gt_t k' r -> gt_t k' (insert k v r)) ->
(forall (l : tree V) (k k' : Z) (v : V), (k < k')%Z -> lt_t k' l -> lt_t k' (insert k v l)) ->
(forall (d : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 lookup d x (Node l y v r) = ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 bound x (Node l y v r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
(forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
(forall (l : tree V) (k : Z) (v : V) (r : tree V),
 (lt_t k l /\ gt_t k r /\ ordered l /\ ordered r -> ordered (Node l k v r)) /\
 (ordered (Node l k v r) -> lt_t k l /\ gt_t k r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
 ((k' > k)%Z /\ gt_t k l /\ gt_t k r -> gt_t k (Node l k' v r)) /\
 (gt_t k (Node l k' v r) -> (k' > k)%Z /\ gt_t k l /\ gt_t k r)) ->
(forall k : Z, gt_t k Emp) ->
(forall (k : Z) (l : tree V) (k' : Z) (v : V) (r : tree V),
 ((k' < k)%Z /\ lt_t k l /\ lt_t k r -> lt_t k (Node l k' v r)) /\
 (lt_t k (Node l k' v r) -> (k' < k)%Z /\ lt_t k l /\ lt_t k r)) ->
(forall k : Z, lt_t k Emp) -> forall (k : Z) (v : V), ordered Emp -> ordered (insert k v Emp)
).

MetaCoq Quote Definition insert_ordered_node := (
  forall (t1 : tree V) (k : Z) (v : V) (t2 : tree V),
(forall (k0 : Z) (v0 : V), ordered t1 -> ordered (insert k0 v0 t1)) ->
(forall (k0 : Z) (v0 : V), ordered t2 -> ordered (insert k0 v0 t2)) ->
(forall (r : tree V) (k0 k' : Z) (v0 : V), (k0 > k')%Z -> gt_t k' r -> ordered r -> ordered (insert k0 v0 r)) ->
(forall (l : tree V) (k0 k' : Z) (v0 : V), (k0 < k')%Z -> lt_t k' l -> ordered l -> ordered (insert k0 v0 l)) ->
(forall (r : tree V) (k0 k' : Z) (v0 : V), (k' < k0)%Z -> gt_t k' r -> gt_t k' (insert k0 v0 r)) ->
(forall (l : tree V) (k0 k' : Z) (v0 : V), (k0 < k')%Z -> lt_t k' l -> lt_t k' (insert k0 v0 l)) ->
(forall (d : V) (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 lookup d x (Node l y v0 r) = ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v0)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 bound x (Node l y v0 r) = ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v0 (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v0 l) y v' r) (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
(forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
(forall (l : tree V) (k0 : Z) (v0 : V) (r : tree V),
 (lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r -> ordered (Node l k0 v0 r)) /\
 (ordered (Node l k0 v0 r) -> lt_t k0 l /\ gt_t k0 r /\ ordered l /\ ordered r)) ->
ordered Emp ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r -> gt_t k0 (Node l k' v0 r)) /\
 (gt_t k0 (Node l k' v0 r) -> (k' > k0)%Z /\ gt_t k0 l /\ gt_t k0 r)) ->
(forall k0 : Z, gt_t k0 Emp) ->
(forall (k0 : Z) (l : tree V) (k' : Z) (v0 : V) (r : tree V),
 ((k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r -> lt_t k0 (Node l k' v0 r)) /\
 (lt_t k0 (Node l k' v0 r) -> (k' < k0)%Z /\ lt_t k0 l /\ lt_t k0 r)) ->
(forall k0 : Z, lt_t k0 Emp) ->
forall (k0 : Z) (v0 : V), ordered (Node t1 k v t2) -> ordered (insert k0 v0 (Node t1 k v t2))
).
(*** MS END {"type": "configuration", "config_type":"boilerplate"} *)

(*** MS BEGIN {"type": "proof_definition"} *)
Theorem insert_ordered : 
forall (t: tree V) k v,
  ordered t -> 
  ordered (insert k v t).
(*** MS END {"type": "proof_definition"} *)
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"manual"} *)
  induction t;
  intros;
  simpl in *.
  - intuition.
  - destruct (k0 <? k)%Z eqn:?;
    simpl in *.
    * intuition.
      eapply insert_left_lt;
      intuition.
    * destruct (k0 >? k)%Z eqn:?;
      simpl in *; 
      intuition.
      + eapply insert_right_lt;
        intuition.
      + assert (k0 = k) by Lia.lia.
        subst.
        trivial.
      + assert (k0 = k) by Lia.lia.
        subst.
        trivial.
(*** MS END {"type": "proof", "proof_type":"manual"} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
  induction t.
  - hammer.
  - admit. (* hammer. *)
(*** MS END {"type": "proof", "proof_type":"hammer", "total":2, "finished":1} *)
  Restart.
Proof.
  (*** MS BEGIN {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
  induction t;
  prep_proof''.
  - reflect insert_ordered_emp; 
    check_goal_unsat.
  - reflect insert_ordered_node; 
    check_goal_unsat.
(*** MS END {"type": "proof", "proof_type":"mirrorsolve", "total":2} *)
Admitted.
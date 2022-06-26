
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

Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.

From Hammer Require Import Hammer.

Set Hammer ATPLimit 5.
Set Hammer ReconstrLimit 10.

Require Import Coq.ZArith.BinInt.

Section Trees.
  (* type of values in the tree *)
  Variable (V: Type).
  Set Universe Polymorphism.

  (* UF symbols for trees: we model lookup, insert, and bound as UFs *)
  
  Notation sig := FOLTrees.sig.

  Definition tree_model := FOLTrees.fm_model V.

  Definition symbs : list (string * list (sig_sorts sig) * sig_sorts sig) := ([
    ("lookup", [TS; ZS; TreeS], TS); 
    ("insert", [ZS; TS; TreeS], TreeS); 
    ("bound", [ZS; TreeS], BS) 
  ]%string).

  Lemma in_conv : forall {sym a r}, 
    In (sym, a, r) symbs -> 
    in_symbs sig sorts_eq_dec symbs sym a r = true.
  Proof.
    eapply UF.in_symbs_corr.
  Defined.

  Import HListNotations.

  (* Interpretation function for UF symbols. 
    In order for the reflection machinery to work out, we need to provide an actual interpretation for the UF symbols (even though they will be discharged as UF symbols in SMT).  *)
  Definition interp_syms (sym: string) (a: list (sig_sorts sig)) (r: sig_sorts sig) (H: In (sym, a, r) symbs) (args: HList.t (FirstOrder.mod_sorts sig tree_model) a) : FirstOrder.mod_sorts sig tree_model r.
    pose proof in_conv H.
    unfold in_symbs in H0.
    simpl in H0.
    repeat match goal with 
    | H: (if (?L =? ?R)%string then _ else _) = _ |- _ => 
      destruct (comp_str_eqb_spec L R)
    | H: (if ?A then _ else _) = _ |- _ => 
      destruct A eqn:?
    end; try congruence;
    subst;
    repeat match goal with 
    | X: HList.t _ _ |- _ => 
      inversion X; subst; clear X
    end.
    - exact (lookup X X1 X0).
    - exact (insert X X1 X0).
    - exact (bound X X1).
  Defined.

  Definition tree_uf_model := UF.fm_model sig tree_model symbs interp_syms.

  Notation sig' := (UF.sig sig symbs).


  Require Import MirrorSolve.Reflection.Core.
  Require Import MirrorSolve.Reflection.FM.
  Require Import MirrorSolve.Reflection.Tactics.

  MetaCoq Quote Definition t_ite := @ite.
  MetaCoq Quote Definition t_zlt := @Z.ltb.
  MetaCoq Quote Definition t_glt := @Z.gtb.
  MetaCoq Quote Definition t_emp := @Emp.
  MetaCoq Quote Definition t_node := @Node.

  MetaCoq Quote Definition t_insert := (@FOLTrees.insert V).
  MetaCoq Quote Definition t_lookup := (@FOLTrees.lookup V).
  MetaCoq Quote Definition t_bound := (@FOLTrees.bound V).

  (* Some match tactics for the meta-interpreter. 
    The meta-interpreter converts these definitions into a reflection procedure between pure Coq goals and FOL terms in the UF + Lists combined theory. 
  *)

  Definition is_emp t := eq_ctor t t_emp.
  Definition is_node t := eq_ctor t t_node.
  Definition is_zlt t := eq_term t t_zlt.
  Definition is_zgt t := eq_term t t_glt.
  Definition is_insert t := eq_ctor t t_insert.
  Definition is_lookup t := eq_ctor t t_lookup.
  Definition is_bound t := eq_ctor t t_bound.

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

  Notation blit := (tacLit sig' tree_uf_model bool_lit).

  Definition match_tacs : list ((term -> bool) * tac_syn sig' tree_uf_model) := [
      ( is_emp, tacFun _ _ (Mk_fun_sym sig' _ _ (CFun _ symbs e_f)))
    ; ( is_node, tacFun _ _ (Mk_fun_sym sig' _ _ (CFun _ symbs t_f)))
    ; ( is_zlt, tacFun _ _ (Mk_fun_sym sig' _ _ (CFun _ symbs z_lt)))
    ; ( is_zgt, tacFun _ _ (Mk_fun_sym sig' _ _ (CFun _ symbs z_gt)))
    ; ( is_cond_b, tacFun _ _ (Mk_fun_sym sig' _ _ (CFun _ symbs cond_b)))
    ; ( is_cond_t, tacFun _ _ (Mk_fun_sym sig' _ _ (CFun _ symbs cond_t)))
    ; ( is_cond_tree, tacFun _ _ (Mk_fun_sym sig' _ _ (CFun _ symbs cond_tree)))
    ; ( is_bool_term, blit 
        (fun b => existT _ BS b) 
        (fun b _ => existT _ BS (TFun sig' (CFun _ symbs (b_lit b)) hnil)))
    ; ( is_lookup, tacFun _ _ (Mk_fun_sym sig' _ _ (UFun (s := "lookup") _ symbs ltac:(solve_uf_membership))))
    ; ( is_bound, tacFun _ _ (Mk_fun_sym sig' _ _ (UFun (s := "bound") _ symbs ltac:(solve_uf_membership))))
    ; ( is_insert, tacFun _ _ (Mk_fun_sym sig' _ _ (UFun (s := "insert") _ symbs ltac:(solve_uf_membership))))
  ].

  (* This is an analogous match but for reflecting Coq types into FOL sorts. *)
  Definition match_inds : list ((term -> bool) * FOLTrees.sorts) := [
      (eq_term t_tree, TreeS)
    ; (eq_term t_V, TS)
    ; (eq_term t_bool, BS)
    ; (eq_term t_Z, ZS)
  ].

  Local Declare ML Module "mirrorsolve".
  RegisterCustomSort TS "A".

  RegisterSMTInd TreeS (SICases [
    ("node"%string, [SIRec; SISort (SInt tt); SISort (SCustom "A"); SIRec]); 
    ("emp"%string, [])
    ]) "A_tree".

  RegisterSMTSort ZS SInt.
  RegisterSMTSort BS SBool.

  (* first argument is the return type, the rest are the argument types *)
  RegisterSMTUF "bound" BS ZS TreeS.
  RegisterSMTUF "lookup" TS TS ZS TreeS.
  RegisterSMTUF "insert" TreeS ZS TS TreeS.

  Transparent denote_tm.

  RegisterSMTFun FOLTrees.z_lt "<" 2.
  RegisterSMTFun FOLTrees.z_gt ">" 2.
  RegisterSMTFun FOLTrees.e_f "emp" 0.
  RegisterSMTFun FOLTrees.t_f "node" 4.
  RegisterSMTFun FOLTrees.cond_b "ite" 3.
  RegisterSMTFun FOLTrees.cond_t "ite" 3.
  RegisterSMTFun FOLTrees.cond_tree "ite" 3.

  RegisterSMTBuiltin FOLTrees.b_lit BoolLit.

  Require Import MirrorSolve.Axioms.

  Ltac check_goal_sat := 
    match goal with 
    | |- ?G => check_interp_pos G; eapply UnsoundAxioms.interp_true
    end.
  Ltac check_goal_unsat := 
    match goal with 
    | |- ?G => check_unsat_neg G; eapply UnsoundAxioms.interp_true
    end.

  Locate pose_all.

  Ltac pose_lookup_axioms := Utils.pose_all (tt, @lookup_emp V, @lookup_node V).
  Ltac pose_bound_axioms := Utils.pose_all (tt, @bound_emp V, @bound_node V).
  Ltac pose_insert_axioms := Utils.pose_all (tt, @insert_emp V, @insert_node V).

  Ltac pose_tree_axioms := pose_lookup_axioms; pose_bound_axioms; pose_insert_axioms.

  Ltac prep_proof := pose_tree_axioms; Utils.revert_all; intros ?.

(* ################################################################# *)
(** * Correctness of BST Operations *)

(** To prove the correctness of [lookup] and [bound], we need
    specifications for them.  We'll study two different techniques for
    that in this chapter. *)

(** The first is called _algebraic specification_.  With it, we write
    down equations relating the results of operations.  For example,
    we could write down equations like the following to specify the
    [+] and [*] operations:

      (a + b) + c = a + (b + c)
      a + b = b + a
      a + 0 = a
      (a * b) * c = a * (b * c)
      a * b = b * a
      a * 1 = a
      a * 0 = 0
      a * (b + c) = a * b + a * c

    For BSTs, let's examine how [lookup] should interact with
    when applied to other operations.  It is easy to see what needs to
    be true for [empty_tree]: looking up any value at all in the empty
    tree should fail and return the default value:

      lookup d k empty_tree = d

    What about non-empty trees?  The only way to build a non-empty
    tree is by applying [insert k v t] to an existing tree [t]. So it
    suffices to describe the behavior of [lookup] on the result of an
    arbitrary [insert] operation. There are two cases.  If we look up
    the same key that was just inserted, we should get the value that
    was inserted with it:

      lookup d k (insert k v t) = v

    If we look up a different key than was just inserted, the insert
    should not affect the answer -- which should be the same as if we
    did the lookup in the original tree before the insert occured:

      lookup d k' (insert k v t) = lookup d k' t      if k <> k'

    These three basic equations specify the correct behavior of maps.
    Let's prove that they hold. *)
  MetaCoq Quote Definition lookup_empty_goal := (
    (forall (d : V) (x : Z) (l : tree V) (y : Z) 
    (v : V) (r : tree V),
  lookup d x (Node l y v r) =
  ite (x <? y)%Z (lookup d x l)
    (ite (x >? y)%Z (lookup d x r) v)) ->
 (forall (d : V) (x : Z), lookup d x Emp = d) ->
 (forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
  bound x (Node l y v r) =
  ite (x <? y)%Z (bound x l)
    (ite (x >? y)%Z (bound x r) true)) ->
 (forall x : Z, bound x Emp = false) ->
 (forall (x : Z) (v : V) (l : tree V) (y : Z) 
    (v' : V) (r : tree V),
  insert x v (Node l y v' r) =
  ite (x <? y)%Z (Node (insert x v l) y v' r)
    (ite (x >? y)%Z (Node l y v' (insert x v r))
       (Node l x v r))) ->
 (forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
 forall (d : V) (k : Z), lookup d k Emp = d
  ).

  (* MetaCoq Quote Definition  *)

  (* hammer handles this one (it's easy) *)
  SetSMTSolver "cvc5".
  Theorem lookup_empty : 
    forall (d: V) (k : Z),
      lookup d k Emp = d.
  Proof.
    prep_proof.
    reflect_goal (UF.sig sig symbs) tree_uf_model sorts_eq_dec match_tacs match_inds lookup_empty_goal. 
    check_goal_unsat.
  Admitted. (* some weird evaluation issue, can't QED... *)


  MetaCoq Quote Definition lookup_insert_emp := (
    (forall (d : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
    lookup d x (Node l y v r) =
    ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v)) ->
   (forall (d : V) (x : Z), lookup d x Emp = d) ->
   (forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
    bound x (Node l y v r) =
    ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
   (forall x : Z, bound x Emp = false) ->
   (forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
    insert x v (Node l y v' r) =
    ite (x <? y)%Z (Node (insert x v l) y v' r)
      (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
   (forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
   forall (d : V) (k : Z) (v : V), lookup d k (insert k v Emp) = v
  ).

  MetaCoq Quote Definition lookup_insert_node := (
    forall (t1 : tree V) (k : Z) (v : V) (t2 : tree V),
    (forall (d : V) (k0 : Z) (v0 : V), lookup d k0 (insert k0 v0 t1) = v0) ->
    (forall (d : V) (k0 : Z) (v0 : V), lookup d k0 (insert k0 v0 t2) = v0) ->
    (forall (d : V) (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
     lookup d x (Node l y v0 r) =
     ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v0)) ->
    (forall (d : V) (x : Z), lookup d x Emp = d) ->
    (forall (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
     bound x (Node l y v0 r) =
     ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
    (forall x : Z, bound x Emp = false) ->
    (forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
     insert x v0 (Node l y v' r) =
     ite (x <? y)%Z (Node (insert x v0 l) y v' r)
       (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
    (forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
    forall (d : V) (k0 : Z) (v0 : V),
    lookup d k0 (insert k0 v0 (Node t1 k v t2)) = v0
  ).


  (* hammer handles this one *)
  Theorem lookup_insert_eq : 
    forall (t : tree V) d k v,
      lookup d k (insert k v t)  = v.
  Proof.
    induction t; prep_proof.
    - reflect_goal (UF.sig sig symbs) tree_uf_model sorts_eq_dec match_tacs match_inds lookup_insert_emp. 
      check_goal_unsat.
    - reflect_goal (UF.sig sig symbs) tree_uf_model sorts_eq_dec match_tacs match_inds lookup_insert_node. 
      check_goal_unsat.
  Admitted.


  MetaCoq Quote Definition lookup_insert_neq_emp := (
    (forall (d : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 lookup d x (Node l y v r) =
 ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 bound x (Node l y v r) =
 ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v l) y v' r)
   (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
(forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
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
     bound x (Node l y v0 r) =
     ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
    (forall x : Z, bound x Emp = false) ->
    (forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
     insert x v0 (Node l y v' r) =
     ite (x <? y)%Z (Node (insert x v0 l) y v' r)
       (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
    (forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
    forall (d : V) (k0 k' : Z) (v0 : V),
    k0 <> k' ->
    lookup d k' (insert k0 v0 (Node t1 k v t2)) = lookup d k' (Node t1 k v t2)
  ).


  (* hammer does not handle this one *)
  Theorem lookup_insert_neq :
    forall (t: tree V) d k k' v,
      k <> k' -> 
      lookup d k' (insert k v t) = lookup d k' t.
  Proof.
    induction t; prep_proof.
    - 
      reflect_goal (UF.sig sig symbs) tree_uf_model sorts_eq_dec match_tacs match_inds lookup_insert_neq_emp. 
      check_goal_unsat.
    - 
      reflect_goal (UF.sig sig symbs) tree_uf_model sorts_eq_dec match_tacs match_inds lookup_insert_neq_node. 
      check_goal_unsat.
  Admitted.

(** **** Exercise: 3 stars, standard, optional (bound_correct) *)

(** Specify and prove the correctness of [bound]. State and prove
    three theorems, inspired by those we just proved for [lookup]. *)

(* FILL IN HERE *)

(** **** Exercise: 3 stars, standard, optional (bound_default) *)

(** Prove that if [bound] returns [false], then [lookup] returns
    the default value. Proceed by induction on the tree. *)


    MetaCoq Quote Definition bound_default_emp := (
      forall (k : Z) (d : V),
      (forall (d0 : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
       lookup d0 x (Node l y v r) =
       ite (x <? y)%Z (lookup d0 x l) (ite (x >? y)%Z (lookup d0 x r) v)) ->
      (forall (d0 : V) (x : Z), lookup d0 x Emp = d0) ->
      (forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
       bound x (Node l y v r) =
       ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
      (forall x : Z, bound x Emp = false) ->
      (forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
       insert x v (Node l y v' r) =
       ite (x <? y)%Z (Node (insert x v l) y v' r)
         (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
      (forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
      bound k Emp = false -> lookup d k Emp = d
    ).
  
  
    MetaCoq Quote Definition bound_default_node := (
      forall (k : Z) (d : V) (t1 : tree V) (k0 : Z) (v : V) (t2 : tree V),
      (bound k t1 = false -> lookup d k t1 = d) ->
      (bound k t2 = false -> lookup d k t2 = d) ->
      (forall (d0 : V) (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
       lookup d0 x (Node l y v0 r) =
       ite (x <? y)%Z (lookup d0 x l) (ite (x >? y)%Z (lookup d0 x r) v0)) ->
      (forall (d0 : V) (x : Z), lookup d0 x Emp = d0) ->
      (forall (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
       bound x (Node l y v0 r) =
       ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
      (forall x : Z, bound x Emp = false) ->
      (forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
       insert x v0 (Node l y v' r) =
       ite (x <? y)%Z (Node (insert x v0 l) y v' r)
         (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
      (forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
      bound k (Node t1 k0 v t2) = false -> lookup d k (Node t1 k0 v t2) = d
    ).

    (* hammer handles this one *)
  Theorem bound_default :
    forall k d (t: tree V),
      bound k t = false ->
      lookup d k t = d.
  Proof.
    induction t; prep_proof. 

    - reflect_goal (UF.sig sig symbs) tree_uf_model sorts_eq_dec match_tacs match_inds bound_default_emp. 
      check_goal_unsat.
    - reflect_goal (UF.sig sig symbs) tree_uf_model sorts_eq_dec match_tacs match_inds bound_default_node. 
      check_goal_unsat.
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



MetaCoq Quote Definition lookup_insert_shadow_emp := (
  (forall (d : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 lookup d x (Node l y v r) =
 ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 bound x (Node l y v r) =
 ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v l) y v' r)
   (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
(forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
forall (v v' d : V) (k k' : Z),
lookup d k' (insert k v (insert k v' Emp)) = lookup d k' (insert k v Emp)
).


MetaCoq Quote Definition lookup_insert_shadow_node := (
  forall (t1 : tree V) (k : Z) (v : V) (t2 : tree V),
(forall (v0 v' d : V) (k0 k' : Z),
 lookup d k' (insert k0 v0 (insert k0 v' t1)) = lookup d k' (insert k0 v0 t1)) ->
(forall (v0 v' d : V) (k0 k' : Z),
 lookup d k' (insert k0 v0 (insert k0 v' t2)) = lookup d k' (insert k0 v0 t2)) ->
(forall (d : V) (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 lookup d x (Node l y v0 r) =
 ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v0)) ->
(forall (d : V) (x : Z), lookup d x Emp = d) ->
(forall (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 bound x (Node l y v0 r) =
 ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v0 (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v0 l) y v' r)
   (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
(forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
forall (v0 v' d : V) (k0 k' : Z),
lookup d k' (insert k0 v0 (insert k0 v' (Node t1 k v t2))) =
lookup d k' (insert k0 v0 (Node t1 k v t2))
).

  (* hammer does not handle this one *)
  Lemma lookup_insert_shadow :
    forall (t: tree V) v v' d k k',
      lookup d k' (insert k v (insert k v' t)) = lookup d k' (insert k v t).
  Proof. 
    induction t; prep_proof.

    - reflect_goal (UF.sig sig symbs) tree_uf_model sorts_eq_dec match_tacs match_inds lookup_insert_shadow_emp. 
      check_goal_unsat.
    - reflect_goal (UF.sig sig symbs) tree_uf_model sorts_eq_dec match_tacs match_inds lookup_insert_shadow_node. 
      check_goal_unsat.
  Admitted.


  MetaCoq Quote Definition lookup_insert_same_emp := (
    forall (k k' : Z) (d : V),
(forall (d0 : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 lookup d0 x (Node l y v r) =
 ite (x <? y)%Z (lookup d0 x l) (ite (x >? y)%Z (lookup d0 x r) v)) ->
(forall (d0 : V) (x : Z), lookup d0 x Emp = d0) ->
(forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 bound x (Node l y v r) =
 ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v l) y v' r)
   (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
(forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
lookup d k' (insert k (lookup d k Emp) Emp) = lookup d k' Emp
  ).
  
  
  MetaCoq Quote Definition lookup_insert_same_node := (
    forall (k k' : Z) (d : V) (t1 : tree V) (k0 : Z) (v : V) (t2 : tree V),
lookup d k' (insert k (lookup d k t1) t1) = lookup d k' t1 ->
lookup d k' (insert k (lookup d k t2) t2) = lookup d k' t2 ->
(forall (d0 : V) (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 lookup d0 x (Node l y v0 r) =
 ite (x <? y)%Z (lookup d0 x l) (ite (x >? y)%Z (lookup d0 x r) v0)) ->
(forall (d0 : V) (x : Z), lookup d0 x Emp = d0) ->
(forall (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
 bound x (Node l y v0 r) =
 ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v0 (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v0 l) y v' r)
   (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
(forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
lookup d k' (insert k (lookup d k (Node t1 k0 v t2)) (Node t1 k0 v t2)) =
lookup d k' (Node t1 k0 v t2)
  ).

  (** **** Exercise: 2 stars, standard, optional (lookup_insert_same) *)

  (* hammer does not handle this one *)
  Lemma lookup_insert_same :
    forall k k' d (t: tree V),
      lookup d k' (insert k (lookup d k t) t) = lookup d k' t.
  Proof. 
    induction t; prep_proof.

    - reflect_goal (UF.sig sig symbs) tree_uf_model sorts_eq_dec match_tacs match_inds lookup_insert_same_emp. 
      check_goal_unsat.
    - reflect_goal (UF.sig sig symbs) tree_uf_model sorts_eq_dec match_tacs match_inds lookup_insert_same_node. 
      check_goal_unsat.
  Admitted.



  MetaCoq Quote Definition lookup_insert_permute_emp := (
    forall (v1 v2 d : V) (k1 k2 k' : Z),
(forall (d0 : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 lookup d0 x (Node l y v r) =
 ite (x <? y)%Z (lookup d0 x l) (ite (x >? y)%Z (lookup d0 x r) v)) ->
(forall (d0 : V) (x : Z), lookup d0 x Emp = d0) ->
(forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
 bound x (Node l y v r) =
 ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
(forall x : Z, bound x Emp = false) ->
(forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
 insert x v (Node l y v' r) =
 ite (x <? y)%Z (Node (insert x v l) y v' r)
   (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
(forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
k1 <> k2 ->
lookup d k' (insert k1 v1 (insert k2 v2 Emp)) =
lookup d k' (insert k2 v2 (insert k1 v1 Emp))
).
  
  
  MetaCoq Quote Definition lookup_insert_permute_node := (
    forall (v1 v2 d : V) (k1 k2 k' : Z) (t1 : tree V) 
    (k : Z) (v : V) (t2 : tree V),
  (k1 <> k2 ->
   lookup d k' (insert k1 v1 (insert k2 v2 t1)) =
   lookup d k' (insert k2 v2 (insert k1 v1 t1))) ->
  (k1 <> k2 ->
   lookup d k' (insert k1 v1 (insert k2 v2 t2)) =
   lookup d k' (insert k2 v2 (insert k1 v1 t2))) ->
  (forall (d0 : V) (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
   lookup d0 x (Node l y v0 r) =
   ite (x <? y)%Z (lookup d0 x l) (ite (x >? y)%Z (lookup d0 x r) v0)) ->
  (forall (d0 : V) (x : Z), lookup d0 x Emp = d0) ->
  (forall (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
   bound x (Node l y v0 r) =
   ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
  (forall x : Z, bound x Emp = false) ->
  (forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
   insert x v0 (Node l y v' r) =
   ite (x <? y)%Z (Node (insert x v0 l) y v' r)
     (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
  (forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
  k1 <> k2 ->
  lookup d k' (insert k1 v1 (insert k2 v2 (Node t1 k v t2))) =
  lookup d k' (insert k2 v2 (insert k1 v1 (Node t1 k v t2)))
  ).

  (** **** Exercise: 2 stars, standard, optional (lookup_insert_permute) *)

  (* hammer does not handle this one *)
  Lemma lookup_insert_permute :
    forall v1 v2 d k1 k2 k' (t: tree V),
      k1 <> k2 ->
      lookup d k' (insert k1 v1 (insert k2 v2 t))
      = lookup d k' (insert k2 v2 (insert k1 v1 t)).
  Proof. 
    induction t; prep_proof.

    - reflect_goal (UF.sig sig symbs) tree_uf_model sorts_eq_dec match_tacs match_inds lookup_insert_permute_emp. 
      check_goal_unsat.
    - reflect_goal (UF.sig sig symbs) tree_uf_model sorts_eq_dec match_tacs match_inds lookup_insert_permute_node. 
      check_goal_unsat.

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


    MetaCoq Quote Definition insert_shadow_equality_emp := (
      (forall (d : V) (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
      lookup d x (Node l y v r) =
      ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v)) ->
     (forall (d : V) (x : Z), lookup d x Emp = d) ->
     (forall (x : Z) (l : tree V) (y : Z) (v : V) (r : tree V),
      bound x (Node l y v r) =
      ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
     (forall x : Z, bound x Emp = false) ->
     (forall (x : Z) (v : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
      insert x v (Node l y v' r) =
      ite (x <? y)%Z (Node (insert x v l) y v' r)
        (ite (x >? y)%Z (Node l y v' (insert x v r)) (Node l x v r))) ->
     (forall (x : Z) (v : V), insert x v Emp = Node Emp x v Emp) ->
     forall (k : Z) (v v' : V), insert k v (insert k v' Emp) = insert k v Emp
  ).
    
    
    MetaCoq Quote Definition insert_shadow_equality_node := (
      forall (t1 : tree V) (k : Z) (v : V) (t2 : tree V),
      (forall (k0 : Z) (v0 v' : V),
       insert k0 v0 (insert k0 v' t1) = insert k0 v0 t1) ->
      (forall (k0 : Z) (v0 v' : V),
       insert k0 v0 (insert k0 v' t2) = insert k0 v0 t2) ->
      (forall (d : V) (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
       lookup d x (Node l y v0 r) =
       ite (x <? y)%Z (lookup d x l) (ite (x >? y)%Z (lookup d x r) v0)) ->
      (forall (d : V) (x : Z), lookup d x Emp = d) ->
      (forall (x : Z) (l : tree V) (y : Z) (v0 : V) (r : tree V),
       bound x (Node l y v0 r) =
       ite (x <? y)%Z (bound x l) (ite (x >? y)%Z (bound x r) true)) ->
      (forall x : Z, bound x Emp = false) ->
      (forall (x : Z) (v0 : V) (l : tree V) (y : Z) (v' : V) (r : tree V),
       insert x v0 (Node l y v' r) =
       ite (x <? y)%Z (Node (insert x v0 l) y v' r)
         (ite (x >? y)%Z (Node l y v' (insert x v0 r)) (Node l x v0 r))) ->
      (forall (x : Z) (v0 : V), insert x v0 Emp = Node Emp x v0 Emp) ->
      forall (k0 : Z) (v0 v' : V),
      insert k0 v0 (insert k0 v' (Node t1 k v t2)) = insert k0 v0 (Node t1 k v t2)
    ).



  (* hammer does not handle this one *)
  Lemma insert_shadow_equality : 
    forall (t: tree V) k v v',
      insert k v (insert k v' t) = insert k v t.
  Proof.
    induction t; prep_proof.

    - reflect_goal (UF.sig sig symbs) tree_uf_model sorts_eq_dec match_tacs match_inds insert_shadow_equality_emp. 
      check_goal_unsat.
    - reflect_goal (UF.sig sig symbs) tree_uf_model sorts_eq_dec match_tacs match_inds insert_shadow_equality_node. 
      check_goal_unsat.
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



(** * SearchTree: Binary Search Trees *)
(* Due to VFA's exercise on binary search trees: 
  https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html
*)

Require Import MirrorSolve.FirstOrder.

Require Import MirrorSolve.BV.
Require Import MirrorSolve.SMT.
Require Import MirrorSolve.UF.

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

Require Import MirrorSolve.Crush.

Ltac hammer' := timeout 60 hammer.
Ltac crush' := timeout 60 crush.

Inductive sorted : list Z -> Prop :=
  | sorted_nil : sorted []
  | sorted_1 : forall x, sorted [x]
  | sorted_cons : forall x y l,
    (x <= y)%Z -> sorted (y :: l) -> sorted (x :: y :: l).

Inductive NoDup_Z : list Z -> Prop :=
  NoDup_nil_z : NoDup_Z []
| NoDup_cons_z : forall (x : Z) (l : list Z),
                ~ In x l -> NoDup_Z l -> NoDup_Z (x :: l).

Lemma nd_z_nil : 
  NoDup_Z [] <-> True.
Proof.
  intuition eauto.
  econstructor.
Qed.

Lemma nd_z_cons : 
  forall (x: Z) (l: list Z), 
    NoDup_Z (x :: l) <-> (~ In x l /\ NoDup_Z l).
Proof.
  intros.
  split; intros.
  - inversion H;
    subst.
    intuition eauto.
  - econstructor.
    intuition eauto.
    destruct H.
    eauto.
Qed.

Definition disjoint (l1 l2: list Z) := forall (x : Z),
  In x l1 -> ~ In x l2.

Lemma disjoint_spec:
  forall l1 l2, disjoint l1 l2 <-> (forall x, In x l1 -> ~ In x l2).
Proof.
  intuition eauto.
Qed.

Section SearchTree.
  Variable (V: Type).
  Notation key := Z.

(** [E] represents the empty map.  [T l k v r] represents the
    map that binds [k] to [v], along with all the bindings in [l] and
    [r].  No key may be bound more than once in the map. *)

  Inductive tree : Type :=
    | E
    | T (l : tree) (k : key) (v : V) (r : tree).

  Equations empty_tree : tree := {empty_tree := E }.

  Local Open Scope Z_scope.

(** [bound k t] is whether [k] is bound in [t]. *)
  Equations bound_t (x : key) (t: tree) : bool := {
    bound_t _ E := false ;
    bound_t x (T l y v r) := 
      ite (x <? y) (bound_t x l) (
      ite (x >? y) (bound_t x r) true
    )
  }.

(** [lookup d k t] is the value bound to [k] in [t], or is default
    value [d] if [k] is not bound in [t]. *)

  Equations lookup_t (d : V) (x : key) (t: tree) : V := {
    lookup_t d _ E := d ;
    lookup_t d x (T l y v r) := 
      ite (x <? y) (lookup_t d x l) (
      ite (x >? y) (lookup_t d x r) v
    );
  }.

(** [insert k v t] is the map containing all the bindings of [t] along
    with a binding of [k] to [v]. *)

  Equations insert_t (x : key) (v: V) (t: tree) : tree := {
    insert_t x v E := T E x v E ;
    insert_t x v (T l y v' r) := 
      ite (x <? y) (T (insert_t x v l) y v' r) (
      ite (x >? y) (T l y v' (insert_t x v r)) (T l x v r)
    );
  }.


(** So, let's formalize the BST invariant. Here's one way to do
    so.  First, we define a helper [ForallT] to express that idea that
    a predicate holds at every node of a tree: *)

  Fixpoint ForallT (P: key -> V -> Prop) (t: tree) : Prop :=
    match t with
    | E => True
    | T l k v r => P k v /\ ForallT P l /\ ForallT P r
    end.

  Fixpoint lt_t (k: Z) (t: tree) : Prop := 
    match t with 
    | E => True
    | T l k' _ r => k' < k /\ lt_t k l /\ lt_t k r
    end. 
  
  Lemma lt_t_spec : forall x t, ForallT (fun y _ => y < x) t <-> lt_t x t.
  Proof.
    induction t; simpl in *; intuition eauto.
  Qed.

  Fixpoint lt_list (k: Z) (t: list (key * V)) : Prop := 
    match t with 
    | [] => True
    | (k', _) :: t' => k' < k /\ lt_list k t'
    end. 

  Fixpoint lt_list_s (k: key) (t: list key) : Prop := 
    match t with 
    | [] => True
    | k' :: t' => k' < k /\ lt_list_s k t'
    end. 

  Fixpoint gt_t (k: Z) (t: tree) : Prop := 
    match t with 
    | E => True
    | T l k' _ r => k' > k /\ gt_t k l /\ gt_t k r
    end. 
  
  Lemma gt_t_spec : forall x t, ForallT (fun y _ => y > x) t <-> gt_t x t.
  Proof.
    induction t; simpl in *; intuition eauto.
  Qed.

  Fixpoint gt_list (k: Z) (t: list (key * V)) : Prop := 
    match t with 
    | [] => True
    | (k', _) :: t' => k' > k /\ gt_list k t'
    end. 
  Fixpoint gt_list_s (k: Z) (t: list key) : Prop := 
    match t with 
    | [] => True
    | k' :: t' => k' > k /\ gt_list_s k t'
    end. 

  (** Second, we define the BST invariant:

      - An empty tree is a BST.

      - A non-empty tree is a BST if all its left nodes have a lesser
        key, its right nodes have a greater key, and the left and
        right subtrees are themselves BSTs. *)

  Inductive BST : tree -> Prop :=
  | BST_E : BST E
  | BST_T : forall l x v r,
      ForallT (fun y _ => y < x) l ->
      ForallT (fun y _ => y > x) r ->
      BST l ->
      BST r ->
      BST (T l x v r).

  (* Hint Constructors BST. *)
  Fixpoint ordered (t: tree) : Prop :=
    match t with 
    | E => True
    | T l k _ r => 
      lt_t k l /\ 
      gt_t k r /\ 
      ordered l /\ ordered r
    end.

  Lemma ordered_spec : 
    forall t, BST t <-> ordered t.
  Proof.
    induction t; simpl in *; intuition eauto;
    try (now econstructor);
    try match goal with 
    | H: BST (_ _ _ _ _) |- _ => inversion H; subst
    end;
    intuition eauto.
    - eapply lt_t_spec; eauto.
    - eapply gt_t_spec; eauto.
    - econstructor; eauto;
      (eapply lt_t_spec || eapply gt_t_spec); eauto.
  Qed.


  (* This is needed for later *)
  Equations elements (t : tree) : list (key * V) := {
    elements E := [] ;
    elements (T l k v r) := elements l ++ [(k, v)] ++ elements r;
  }.

  Equations map_fst (xs : list (key * V)) : list key := {
    map_fst [] := [] ;
    map_fst ((x, _) :: xs) := x :: map_fst xs;
  }.

  Equations fast_elements_tr (t: tree) (acc : list (key * V)) : list (key * V) := {
    fast_elements_tr E acc := acc ;
    fast_elements_tr (T l k v r) acc := fast_elements_tr l ((k, v) :: fast_elements_tr r acc);
  }.

  Equations fast_elements (t : tree) : list (key * V) := { 
    fast_elements t := fast_elements_tr t [];
  }.

  Equations kvs_insert (k : key) (v : V) (kvs : list (key * V)) : list (key * V) := {
    kvs_insert k v [] := [(k, v)] ;
    kvs_insert k v ((k', v') :: kvs') := 
      ite (k <? k') ((k, v) :: (k', v') :: kvs') (
      ite (k >? k') ((k', v') :: kvs_insert k v kvs') (
        (k, v) :: kvs'
      ));
  }.

  Declare ML Module "mirrorsolve".

  From MetaCoq.Template Require Import All Loader.
  Import MCMonadNotation.
  Require Import MirrorSolve.Config.
  Open Scope bs.

  (* MirrorSolve's automation needs this later. *)
  Universe foo.
  MetaCoq Quote Definition typ_term := Type@{foo}.

  Notation pack x := (existT _ _ x).

  Definition fun_syms : list packed := ([
      pack bound_t
    ; pack lookup_t
    ; pack insert_t
    ; pack tree
    ; pack (key * V)
    ; pack (list (key * V))
    ; pack (list key)
    ; pack (list V)
    ; pack map_fst
    ; pack (@List.app (key * V))
    ; pack (@List.app key)
    ; pack Z.ltb
    ; pack Z.gtb
    ; pack empty_tree
    ; pack (@ite tree)
    ; pack (@ite V)
    ; pack (@ite bool)
    ; pack (@ite (list (key * V)))
    ; pack elements
    ; pack fast_elements
    ; pack fast_elements_tr
    ; pack kvs_insert
  ])%type.

  Definition rel_syms : list packed := ([ 
        pack BST
      ; pack ordered
      ; pack lt_t
      ; pack gt_t
      ; pack Z.lt
      ; pack Z.gt
      ; pack (@List.In (key * V))
      ; pack (@List.In key)
      ; pack lt_list
      ; pack gt_list
      ; pack lt_list_s
      ; pack gt_list_s
      ; pack sorted
      ; pack (Z.le)
      ; pack NoDup_Z
      ; pack disjoint
  ])%type.

  Definition prim_syms : list (packed * String.string) := [
      (pack Z.add, "+"%string)
    ; (pack Z.lt, "<"%string)
    ; (pack Z.gt, ">"%string)
    ; (pack Z.ltb, "<"%string)
    ; (pack Z.gtb, ">"%string)
    ; (pack Z.le, "<="%string)
    ; (pack (@ite bool), "ite"%string)
    ; (pack (@ite tree), "ite"%string)
    ; (pack (@ite V), "ite"%string)
    ; (pack (@ite (list (key * V))), "ite"%string)
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

  Create HintDb tree_eqns.

  Ltac prep_proof := 
    hints_foreach (fun x => pose proof x) "tree_eqns";
    Utils.revert_all;
    unfold "<->" in *.

  Scheme Equality for sorts.

  Ltac quote_reflect_tree := quote_reflect sig fm_model sorts_eq_dec match_tacs match_sorts.

  Ltac mirrorsolve :=
    prep_proof;
    quote_reflect_tree;
    check_goal_unsat. 

  SetSMTSolver "z3".

  Hint Immediate ordered_spec : tree_eqns. 

  (*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
  Lemma ordered_emp: 
    ordered E.
  Proof. 
    intros; 
    simpl; 
    intuition. 
  Qed.

  Lemma ordered_node: 
    forall l k v r, 
      (lt_t k l /\ 
      gt_t k r /\ 
      ordered l /\ ordered r) <->
      ordered (T l k v r).
  Proof. 
    intros; 
    simpl; 
    intuition. 
  Qed.

  Hint Immediate ordered_emp : tree_eqns. 
  Hint Immediate ordered_node : tree_eqns. 
  (*** MS END {"type": "configuration", "config_type":"boilerplate"} *)
    

(** **** Exercise: 1 star, standard (empty_tree_BST) *)

(** Prove that the empty tree is a BST. *)

  Theorem empty_tree_BST : 
      BST E.
  Proof.
    mirrorsolve.
  Qed.

(** [] *)

(** **** Exercise: 4 stars, standard (insert_BST) *)

(** Prove that [insert] produces a BST, assuming it is given one.

    Start by proving this helper lemma, which says that [insert]
    preserves any node predicate. Proceed by induction on [t]. *)

  (* We can't prove the helper predicate because it's about the higher-order thing of ForallT *)

Lemma ForallT_insert : forall (P : key -> V -> Prop) (t : tree),
    ForallT P t -> forall (k : key) (v : V),
      P k v -> ForallT P (insert_t k v t).
Proof.
  (* FILL IN HERE *) Admitted.

(* But we can prove the corresponding properties for lt_t and gt_t.
*)

  (* first, reflect lt_t and gt_t: *)

  (*** MS BEGIN {"type": "configuration", "config_type":"boilerplate"} *)
  Lemma lt_emp: 
    forall x, lt_t x E <-> True.
  Proof. 
    intros; 
    simpl; 
    intuition. 
  Qed.

  Lemma lt_node: 
    forall x l k v r, 
      (lt_t x l /\ 
       lt_t x r /\
       k < x) <->
      lt_t x (T l k v r).
  Proof. 
    intros; 
    simpl; 
    intuition. 
  Qed.

  Hint Immediate lt_emp : tree_eqns. 
  Hint Immediate lt_node : tree_eqns. 

  Lemma gt_emp: 
    forall x, gt_t x E <-> True.
  Proof. 
    intros; 
    simpl; 
    intuition. 
  Qed.

  Lemma gt_node: 
    forall x l k v r, 
      (gt_t x l /\ 
       gt_t x r /\
       k > x) <->
      gt_t x (T l k v r).
  Proof. 
    intros; 
    simpl; 
    intuition. 
  Qed.

  Hint Immediate gt_emp : tree_eqns. 
  Hint Immediate gt_node : tree_eqns. 


  Hint Immediate gt_emp : tree_eqns. 
  Hint Immediate gt_node : tree_eqns. 

  Hint Immediate insert_t_equation_1 : tree_eqns.
  Hint Immediate insert_t_equation_2 : tree_eqns.
  (*** MS END {"type": "configuration", "config_type":"boilerplate"} *)


  Lemma gt_t_trans : 
    forall (x y : Z), 
      x > y -> 
      forall t, gt_t x t -> gt_t y t.
  Proof.
    (* induction t;
    try hammer.
    Restart.  *)
    (* hammer and crush both worked! *)
    induction t;
    mirrorsolve.
  Qed.

  Lemma lt_t_trans : 
    forall (x y : Z), 
      x < y -> 
      forall t, lt_t x t -> lt_t y t.
  Proof.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate lt_t_trans : tree_eqns.
  Hint Immediate gt_t_trans : tree_eqns.

  Hint Immediate Z.ltb_lt : tree_eqns.
  
  Lemma gtb_gt : 
    forall (x y: Z), (x >? y = true) <-> x > y.
  Proof.
    Lia.lia.
  Qed.
  Hint Immediate gtb_gt : tree_eqns.

  Lemma lt_t_insert : 
    forall t x k, 
      lt_t x t->
      k < x -> 
      forall v, 
        lt_t x (insert_t k v t).
  Proof.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate lt_t_insert : tree_eqns.

  Lemma gt_t_insert : 
    forall t x k, 
      gt_t x t->
      k > x -> 
      forall v, 
        gt_t x (insert_t k v t).
  Proof.
    induction t;
    mirrorsolve.
  Qed.
  Hint Immediate gt_t_insert : tree_eqns.

  Lemma ordered_insert : 
    forall t x k, 
      ordered t -> ordered (insert_t k x t).
  Proof.
    (* induction t;
    try hammer.
    Restart.
    induction t;
    try crush.
    Restart. *)
    (* hammer and crush did not work here *)
    induction t;
    mirrorsolve.
  Qed.
  Hint Immediate ordered_insert : tree_eqns.


(** Now prove the main theorem. Proceed by induction on the evidence
    that [t] is a BST. *)

  Theorem insert_BST : forall (k : key) (v : V) (t : tree),
      BST t -> BST (insert_t k v t).
  Proof.
    induction t;
    mirrorsolve.
  Qed.
  Hint Immediate insert_BST : tree_eqns.

(** [] *)

(** Since [empty_tree] and [insert] are the only operations that
    create BSTs, we are guaranteed that any [tree] is a BST -- unless
    it was constructed manually with [T].  It would therefore make
    sense to limit the use of [T] to only within the tree operations,
    rather than expose it.  Coq, like OCaml and other functional
    languages, can do this with its module system.  See [ADT] for
    details. *)

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

  
  Hint Immediate empty_tree_equation_1 : tree_eqns.
  Hint Immediate lookup_t_equation_1 : tree_eqns.
  Hint Immediate lookup_t_equation_2 : tree_eqns.

  Theorem lookup_empty : forall (d : V) (k : key),
      lookup_t d k empty_tree = d.
  Proof.
    mirrorsolve.
  Qed.

  Theorem lookup_insert_eq : forall (t : tree) (d : V) (k : key) (v : V),
      lookup_t d k (insert_t k v t)  = v.
  Proof.
    induction t; 
    mirrorsolve.
  Qed.

  Hint Immediate lookup_insert_eq : tree_eqns.
  Hint Immediate lookup_empty : tree_eqns.


(** The basic method of that proof is to repeatedly [bdestruct]
    everything in sight, followed by generous use of [lia] and
    [auto]. Let's automate that. *)


(** The tactic immediately pays off in proving the third
    equation. *)

  Theorem lookup_insert_neq :
    forall (t : tree) (d : V) (k k' : key) (v : V),
    k <> k' -> lookup_t d k' (insert_t k v t) = lookup_t d k' t.
  Proof.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate lookup_insert_neq : tree_eqns.

(** Perhaps surprisingly, the proofs of these results do not
    depend on whether [t] satisfies the BST invariant.  That's because
    [lookup] and [insert] follow the same path through the tree, so
    even if nodes are in the "wrong" place, they are consistently
    "wrong". *)

(** **** Exercise: 3 stars, standard, optional (bound_correct) *)

(** Specify and prove the correctness of [bound]. State and prove
    three theorems, inspired by those we just proved for [lookup]. If
    you have the right theorem statements, the proofs should all be
    quite easy -- thanks to [bdall]. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_bound_correct : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (bound_default) *)

(** Prove that if [bound] returns [false], then [lookup] returns
    the default value. Proceed by induction on the tree. *)

  Hint Immediate bound_t_equation_1 : tree_eqns.
  Hint Immediate bound_t_equation_2 : tree_eqns.

  Theorem bound_default :
    forall (t: tree) (k : key) (d : V),
      bound_t k t = false ->
      lookup_t d k t = d.
  Proof.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate bound_default : tree_eqns.

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

  Lemma lookup_insert_shadow :
    forall (t : tree) (v v' d: V) (k k' : key),
      lookup_t d k' (insert_t k v (insert_t k v' t)) = lookup_t d k' (insert_t k v t).
  Proof.
    induction t;
    mirrorsolve.
  Qed.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (lookup_insert_same) *)

  Lemma lookup_insert_same :
    forall (t : tree) (k k' : key) (d : V),
      lookup_t d k' (insert_t k (lookup_t d k t) t) = lookup_t d k' t.
  Proof.
    induction t; 
    mirrorsolve.
  Qed.

  Hint Immediate lookup_insert_same : tree_eqns.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (lookup_insert_permute) *)

  Lemma lookup_insert_permute :
    forall (t: tree) (v1 v2 d : V) (k1 k2 k': key),
      k1 <> k2 ->
      lookup_t d k' (insert_t k1 v1 (insert_t k2 v2 t))
      = lookup_t d k' (insert_t k2 v2 (insert_t k1 v1 t)).
  Proof.
    induction t; 
    mirrorsolve.
  Qed.

  Hint Immediate lookup_insert_permute : tree_eqns.
(** [] *)

(** Our ability to prove these lemmas without reference to the
    underlying tree implementation demonstrates they hold for any map
    implementation that satisfies the three basic equations. *)

(** Each of these lemmas just proved was phrased as an equality
    between the results of looking up an arbitrary key [k'] in two
    maps.  But the lemmas for the function-based maps were phrased as
    direct equalities between the maps themselves.

    Could we state the tree lemmas with direct equalities?  For
    [insert_shadow], the answer is yes: *)

  Lemma insert_shadow_equality : forall (t : tree) (k : key) (v v' : V),
      insert_t k v (insert_t k v' t) = insert_t k v t.
  Proof.
    induction t; mirrorsolve.
  Qed.

  Hint Immediate insert_shadow_equality : tree_eqns.

(** But the other two direct equalities on BSTs do not necessarily
    hold. *)

(** **** Exercise: 3 stars, standard, optional (direct_equalities_break) *)

(** Prove that the other equalities do not hold.  Hint: find a counterexample
    first on paper, then use the [exists] tactic to instantiate the theorem
    on your counterexample.  The simpler your counterexample, the simpler
    the rest of the proof will be. *)

    (* MIRRORSOLVE: We can't prove these because they use exists *)
Lemma insert_same_equality_breaks :
  exists (d : V) (t : tree) (k : key),
      insert_t k (lookup_t d k t) t <> t.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma insert_permute_equality_breaks :
  exists (v1 v2 : V) (k1 k2 : key) (t : tree),
    k1 <> k2 /\ insert_t k1 v1 (insert_t k2 v2 t) <> insert_t k2 v2 (insert_t k1 v1 t).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * Converting a BST to a List *)

(** Let's add a new operation to our BST: converting it to an
    _association list_ that contains the key--value bindings from the
    tree stored as pairs.  If that list is sorted by the keys, then
    any two trees that represent the same map would be converted to
    the same list. Here's a function that does so with an in-order
    traversal of the tree: *)

  (* Equations elements (t : tree) : list (key * V) := {
    elements E := [] ;
    elements (T l k v r) := elements l ++ [(k, v)] ++ elements r;
  }. *)

(** Here are three desirable properties for [elements]:

    1. The list has the same bindings as the tree.

    2. The list is sorted by keys.

    3. The list contains no duplicate keys.

    Let's formally specify and verify them. *)

(* ================================================================= *)
(** ** Part 1: Same Bindings *)

(** We want to show that a binding is in [elements t] iff it's in
    [t]. We'll prove the two directions of that bi-implication
    separately:

    - [elements] is _complete_: if a binding is in [t] then it's in
      [elements t].

    - [elements] is _correct_: if a binding is in [elements t] then
      it's in [t].  *)

(** **** Exercise: 3 stars, standard (elements_complete) *)

(** Prove that [elements] is complete. Proceed by induction on [t]. *)

  Hint Immediate elements_equation_1 : tree_eqns.
  Hint Immediate elements_equation_2 : tree_eqns.

  Lemma In_nil : 
    forall (x : key * V), 
      In x [] <-> False.
  Proof.
    intuition eauto.
  Qed.

  Lemma In_cons : 
    forall (x : key * V) x' xs, 
      In x (x' :: xs) <-> (x = x' \/ In x xs).
  Proof.
    intros;
    simpl in *;
    intuition eauto.
  Qed.

  Hint Immediate In_cons : tree_eqns.
  Hint Immediate In_nil : tree_eqns.

  Lemma in_app_iff' :  
    forall l l' (a:(key * V)), In a (l++l') <-> In a l \/ In a l'.
  Proof.
    eapply in_app_iff.
  Qed.

  Hint Immediate in_app_iff' : tree_eqns.

  Theorem elements_complete : 
    forall (t: tree) (k : key) (v d : V),
      bound_t k t = true ->
      lookup_t d k t = v ->
      In (k, v) (elements t).
  Proof.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate elements_complete : tree_eqns.

(** [] *)

(** Proving correctness requires more work than completeness.

    [BST] uses [ForallT] to say that all nodes in the left/right
    subtree have smaller/greater keys than the root.  We need to
    relate [ForallT], which expresses that all nodes satisfy a
    property, to [Forall], which expresses that all list elements
    satisfy a property.

    The standard library contains a helpful lemma about [Forall]: *)

Check Forall_app. 

(** **** Exercise: 2 stars, standard (elements_preserves_forall) *)

(** Prove that if a property [P] holds of every node in a tree [t],
    then that property holds of every pair in [elements t]. Proceed
    by induction on [t].

    There is a little mismatch between the type of [P] in [ForallT]
    and the type of the property accepted by [Forall], so we have to
    _uncurry_ [P] when we pass it to [Forall]. (See [Poly] for
    more about uncurrying.) The single quote used below is the Coq
    syntax for doing a pattern match in the function arguments. *)

Definition uncurry {X Y Z : Type} (f : X -> Y -> Z) '(a, b) :=
  f a b.

Hint Transparent uncurry.

(* MIRRORSOLVE: We can't do this because of ForallT *)
Lemma elements_preserves_forall : forall (P : key -> V -> Prop) (t : tree),
    ForallT P t ->
    Forall (uncurry P) (elements t).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, standard (elements_preserves_relation) *)

(** Prove that if all the keys in [t] are in a relation [R] with a
    distinguished key [k'], then any key [k] in [elements t] is also
    related by [R] to [k']. For example, [R] could be [<], in which
    case the lemma says that if all the keys in [t] are less than
    [k'], then all the keys in [elements t] are also less than
    [k'].

    Hint: you don't need induction.  Immediately look for a way
    to use [elements_preserves_forall] and library theorem
    [Forall_forall]. *)

(* MIRRORSOLVE: We can't do this because it's higher-order *)
Lemma elements_preserves_relation :
  forall (k k' : key) (v : V) (t : tree) (R : key -> key -> Prop),
    ForallT (fun y _ => R y k') t
    -> In (k, v) (elements t)
    -> R k k'.
Proof.
  (* FILL IN HERE *) Admitted.


  Lemma lt_list_nil : 
    forall x, lt_list x [] <-> True.
  Proof.
    intros;
    simpl in *;
    intuition eauto.
  Qed.

  Lemma lt_list_cons : 
    forall x y v l, lt_list x ((y, v) :: l)  <-> (y < x /\ lt_list x l).
  Proof.
    intros;
    simpl in *;
    intuition eauto.
  Qed.

  Lemma gt_list_nil : 
    forall x, gt_list x [] <-> True.
  Proof.
    intros;
    simpl in *;
    intuition eauto.
  Qed.

  Lemma gt_list_cons : 
    forall x y v l, gt_list x ((y, v) :: l)  <-> (y > x /\ gt_list x l).
  Proof.
    intros;
    simpl in *;
    intuition eauto.
  Qed.

  Hint Immediate lt_list_nil : tree_eqns.
  Hint Immediate lt_list_cons : tree_eqns.
  Hint Immediate gt_list_nil : tree_eqns.
  Hint Immediate gt_list_cons : tree_eqns.

  (* However, we can prove that it preserves lt_t and gt_t, as well as that lt_list and gt_list are transitive *)

  Lemma lt_list_trans : 
    forall l x y,
      x < y -> 
      lt_list x l -> 
      lt_list y l.
  Proof.
    induction l;
    mirrorsolve.
  Qed.

  Lemma gt_list_trans : 
    forall l x y,
      x > y -> 
      gt_list x l -> 
      gt_list y l.
  Proof.
    induction l;
    mirrorsolve.
  Qed.

  Hint Immediate lt_list_trans : tree_eqns.
  Hint Immediate gt_list_trans : tree_eqns.

  SetSMTSolver "z3".

  Lemma lt_list_In : 
    forall x l, 
      lt_list x l <-> (forall y v, In (y, v) l -> y < x).
  Proof.
    induction l;
    mirrorsolve.
  Qed.

  

  Lemma gt_list_In : 
    forall x l, 
      gt_list x l <-> (forall y v, In (y, v) l -> y > x).
  Proof.
    induction l;
    mirrorsolve.
  Qed.

  Hint Immediate lt_list_In : tree_eqns.
  Hint Immediate gt_list_In : tree_eqns.


  Lemma lt_t_elements : 
    forall t x,
      lt_t x t <-> lt_list x (elements t).
  Proof.
    induction t;
    try mirrorsolve.
  Qed.

  Lemma gt_t_elements : 
    forall t x,
      gt_t x t <-> gt_list x (elements t).
  Proof.
    induction t;
    try mirrorsolve.
  Qed.

  Hint Immediate lt_t_elements : tree_eqns.
  Hint Immediate gt_t_elements : tree_eqns.


(** [] *)

(** **** Exercise: 4 stars, standard (elements_correct) *)

(** Prove that [elements] is correct. Proceed by induction on the
    evidence that [t] is a BST. *)

  Theorem elements_correct : 
    forall (t : tree) (k : key) (v d : V),
      BST t ->
      In (k, v) (elements t) ->
      bound_t k t = true /\ lookup_t d k t = v.
  Proof.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate elements_correct : tree_eqns.

(** [] *)

(** The inverses of completeness and correctness also should hold:

    - inverse completeness: if a binding is not in [t] then it's not
      in [elements t].

    - inverse correctness: if a binding is not in [elements t] then
      it's not in [t].

    Let's prove that they do. *)

(** **** Exercise: 2 stars, advanced (elements_complete_inverse) *)

(** This inverse doesn't require induction.  Look for a way to use
    [elements_correct] to quickly prove the result. *)

  Theorem elements_complete_inverse :
    forall (t : tree) (k : key) (v : V) ,
      BST t -> 
      bound_t k t = false ->
      ~ In (k, v) (elements t).
  Proof.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate elements_complete_inverse : tree_eqns.

(** [] *)

(** **** Exercise: 4 stars, advanced (elements_correct_inverse) *)

(** Prove the inverse.  First, prove this helper lemma by induction on
    [t]. *)

(* We can't prove this because there's an exists *)
Lemma bound_value : forall (k : key) (t : tree),
    bound_t k t = true -> exists v, forall d, lookup_t d k t = v.
Proof.
  (* FILL IN HERE *) Admitted.

(** Prove the main result.  You don't need induction. *)

  Theorem elements_correct_inverse :
    forall (t : tree) (k : key) ,
      (forall v, ~ In (k, v) (elements t)) ->
      bound_t k t = false.
  Proof.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate elements_correct_inverse : tree_eqns.

  
(* ================================================================= *)
(** ** Part 2: Sorted (Advanced) *)

(** We want to show that [elements] is sorted by keys.  We follow a
    proof technique contributed by Lydia Symmons et al.*)

(** **** Exercise: 3 stars, advanced (sorted_app) *)

  (* First we reflect the definition of sorted to UF: *)

  Lemma sorted_nil' : 
    sorted [] <-> True.
  Proof.
    intros;
    simpl;
    intuition eauto.
    econstructor.
  Qed.

  Lemma sorted_one' :
    forall x, 
    sorted [x] <-> True.
  Proof.
    intros;
    simpl;
    intuition eauto.
    econstructor.
  Qed.

  Lemma sorted_cons' : 
    forall (x y : key) (l : list key),
      sorted (x :: y :: l) <-> (x <= y /\ sorted (y :: l)).
  Proof.
    intros;
    simpl;
    intuition eauto;
    try match goal with 
    | H: sorted (_ :: _ :: _) |- _ => inversion H; subst
    end;
    eauto.
    econstructor;
    eauto.
  Qed.

  Hint Immediate sorted_nil' : tree_eqns.
  Hint Immediate sorted_one' : tree_eqns.
  Hint Immediate sorted_cons' : tree_eqns.

  Lemma lt_list_s_nil : 
    forall x, lt_list_s x [] <-> True.
  Proof.
    intros;
    simpl in *;
    intuition eauto.
  Qed.

  Lemma lt_list_s_cons : 
    forall l x y, lt_list_s x (y :: l)  <-> (y < x /\ lt_list_s x l).
  Proof.
    intros;
    simpl in *;
    intuition eauto.
  Qed.

  Hint Immediate lt_list_s_nil : tree_eqns.
  Hint Immediate lt_list_s_cons : tree_eqns.
  
  Lemma app_nil_l_Z : 
    forall (x: list key), ([] ++ x = x)%list.
  Proof.
    eapply app_nil_l.
  Qed.

  Lemma app_cons_l_Z : 
    forall (x: key) y z, ((x :: y) ++ z = x :: (y ++ z))%list.
  Proof.
    intros;
    intuition eauto.
  Qed.

  Hint Immediate app_nil_l_Z : tree_eqns.
  Hint Immediate app_cons_l_Z : tree_eqns.

  Lemma sorted_lt_end : 
    forall l x, 
      lt_list_s x l -> 
      sorted l -> 
      sorted (l ++ [x]).
  Proof.
    
    induction l;
    try mirrorsolve.
  Qed.

  Hint Immediate sorted_lt_end : tree_eqns.

  Lemma gt_list_s_nil : 
    forall x, gt_list_s x [] <-> True.
  Proof.
    intros;
    simpl in *;
    intuition eauto.
  Qed.

  Lemma gt_list_s_cons : 
    forall l x y, gt_list_s x (y :: l)  <-> (y > x /\ gt_list_s x l).
  Proof.
    intros;
    simpl in *;
    intuition eauto.
  Qed.

  Hint Immediate gt_list_s_nil : tree_eqns.
  Hint Immediate gt_list_s_cons : tree_eqns.

  Lemma sorted_gt_beginning : 
    forall r x, 
      gt_list_s x r -> 
      sorted r -> 
      sorted (x :: r).
  Proof.
    induction r;
    mirrorsolve.
  Qed.

  Hint Immediate sorted_gt_beginning : tree_eqns.


(** Prove that inserting an intermediate value between two lists
    maintains sortedness. Proceed by induction on the evidence
    that [l1] is sorted. *)

(* We can't prove this because of Forall, but we can replace Forall and prove something about that *)
  Lemma sorted_app: forall l1 l2 x,
    sorted l1 -> sorted l2 ->
    Forall (fun n => n < x) l1 -> Forall (fun n => n > x) l2 ->
    sorted (l1 ++ x :: l2).
  Proof.
    (* FILL IN HERE *) Admitted.

  Lemma sorted_app': forall l1 l2 x,
   sorted l1 ->sorted l2 ->
    lt_list_s x l1 -> gt_list_s x l2 ->
   sorted (l1 ++ x :: l2).
  Proof.
    induction l1;
    induction l2;
    mirrorsolve.
  Qed.

  Hint Immediate sorted_app' : tree_eqns.

(** [] *)

(** **** Exercise: 4 stars, advanced (sorted_elements) *)

(** The keys in an association list are the first elements of every
    pair: *)

  Definition list_keys (lst : list (key * V)) :=
    map fst lst.

(** Prove that [elements t] is sorted by keys. Proceed by induction
    on the evidence that [t] is a BST. *)

  (* We can't directly prove this because of map, but we can replace it with map_fst *)
  Theorem sorted_elements : forall (t : tree),
      BST t -> sorted (list_keys (elements t)).
  Proof.
  (* FILL IN HERE *) Admitted.

  Hint Immediate map_fst_equation_1 : tree_eqns.
  Hint Immediate map_fst_equation_2 : tree_eqns.

  Lemma map_fst_lts : 
    forall l x, 
      lt_list x l <-> lt_list_s x (map_fst l).
  Proof.
    induction l;
    mirrorsolve. 
  Qed.

  Lemma map_fst_gts : 
    forall l x, 
      gt_list x l <-> gt_list_s x (map_fst l).
  Proof.
    induction l;
    mirrorsolve. 
  Qed.

  Hint Immediate map_fst_lts : tree_eqns.
  Hint Immediate map_fst_gts : tree_eqns.

  Lemma app_nil_l_Z_V : 
    forall (x: list (key * V)), ([] ++ x = x)%list.
  Proof.
    eapply app_nil_l.
  Qed.

  Lemma app_cons_l_Z_V : 
    forall (x: (key * V)) y z, ((x :: y) ++ z = x :: (y ++ z))%list.
  Proof.
    intros;
    intuition eauto.
  Qed.

  Hint Immediate app_nil_l_Z_V : tree_eqns.
  Hint Immediate app_cons_l_Z_V : tree_eqns.

  SetSMTSolver "cvc5".

  Lemma map_fst_app :
    forall x y, 
      (map_fst (x ++ y) = map_fst x ++ map_fst y)%list.
  Proof.
    induction x; 
    mirrorsolve.
  Qed. 

  Hint Immediate map_fst_app : tree_eqns.

  Theorem sorted_elements' : forall (t : tree),
      BST t -> sorted (map_fst (elements t)).
  Proof.
    induction t;
    mirrorsolve.
  Qed.

  Hint Resolve sorted_elements' : tree_eqns.

(** [] *)

(* ================================================================= *)
(** ** Part 3: No Duplicates (Advanced and Optional) *)

(** We want to show that [elements t] contains no duplicate
    key bindings. Tree [t] itself cannot contain any duplicates, so the
    list that [elements] produces shouldn't either. The standard
    library already contains a helpful inductive proposition,
    [NoDup]. *)

(** The library is missing a theorem, though, about [NoDup] and [++].
    To state that theorem, we first need to formalize what it means
    for two lists to be disjoint: *)

  Hint Immediate disjoint_spec : tree_eqns.
  Hint Immediate nd_z_nil : tree_eqns.
  Hint Immediate nd_z_cons : tree_eqns.

  Lemma In_nil_Z : 
    forall (x : key), 
      In x [] <-> False.
  Proof.
    intros;
    simpl in *;
    intuition eauto.
  Qed.

  Lemma In_cons_Z : 
    forall (x : key) x' xs, 
      In x (x' :: xs) <-> (x = x' \/ In x xs).
  Proof.
    intros;
    simpl in *;
    intuition eauto.
  Qed.

  Hint Immediate In_cons_Z : tree_eqns.
  Hint Immediate In_nil_Z : tree_eqns.

(** **** Exercise: 3 stars, advanced, optional (NoDup_append) *)

(** Prove that if two lists are disjoint, appending them preserves
    [NoDup].  Hint: You might already have proved this theorem in an
    advanced exercise in [IndProp]. *)

  Lemma disjoint_cons: 
    forall x l r, 
      disjoint (x :: l) r -> disjoint l r.
  Proof.
    induction l;
    mirrorsolve.
  Qed.
  
  Hint Immediate disjoint_cons : tree_eqns.

  Lemma neg_In_app : 
    forall (x: Z) l r, 
      ~ In x l -> ~ In x r -> ~ In x (l ++ r).
  Proof.
    induction l;
    mirrorsolve.
  Qed.

  Hint Immediate neg_In_app : tree_eqns.



  Lemma NoDup_append : forall (l1 l2: list Z),
    NoDup_Z l1 -> NoDup_Z l2 -> disjoint l1 l2 ->
    NoDup_Z (l1 ++ l2).
  Proof.
    induction l1;
    mirrorsolve.
  Qed.

  Hint Immediate NoDup_append : tree_eqns.

  Lemma Not_In_nil : 
    forall (x: key), ~ In x [].
  Proof.
    mirrorsolve.
  Qed.

  Lemma Not_In_cons:
    forall l (x: key) x', 
      ~ In x (x' :: l) <-> (x <> x' /\ ~ In x l).
  Proof.
    induction l;
    mirrorsolve.
  Qed.

  Hint Immediate Not_In_nil : tree_eqns.
  Hint Immediate Not_In_cons : tree_eqns.

  Lemma gt_t_notin : 
    forall l x, 
      gt_list_s x l -> ~ In x l.
  Proof.
    induction l;
    mirrorsolve.
  Qed.

  Lemma lt_t_notin : 
    forall l x, 
      lt_list_s x l -> ~ In x l.
  Proof.
    induction l;
    mirrorsolve.
  Qed.

  Hint Immediate gt_t_notin : tree_eqns.
  Hint Immediate lt_t_notin : tree_eqns.


  Lemma gt_t_disjoint : 
    forall l2 l1, 
      (forall x, In x l1 -> 
      gt_list_s x l2) -> 
      disjoint l1 l2.
  Proof.
    mirrorsolve.
  Qed.

  Lemma lt_t_disjoint : 
    forall l2 l1, 
      (forall x, In x l1 -> 
      lt_list_s x l2) -> 
      disjoint l1 l2.
  Proof.
    mirrorsolve.
  Qed.
  
  Hint Immediate lt_t_disjoint : tree_eqns.
  Hint Immediate gt_t_disjoint : tree_eqns.

(** [] *)

(** **** Exercise: 4 stars, advanced, optional (elements_nodup_keys) *)

(** Prove that there are no duplicate keys in the list returned
    by [elements]. Proceed by induction on the evidence that [t] is a
    BST. Make use of library theorems about [map] as needed. *)

    (* We can't prove this because it uses map and nodup, but we can prove one with map_fst and nodup_z! *)
  Theorem elements_nodup_keys : forall (t : tree),
    BST t ->
    NoDup (list_keys (elements t)).
  Proof.
  (* FILL IN HERE *) Admitted.

  Theorem elements_nodup_keys' : forall (t : tree),
    ordered t ->
    NoDup_Z (map_fst (elements t)).
  Proof.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate elements_nodup_keys' : tree_eqns.

(** [] *)

(** That concludes the proof of correctness of [elements]. *)

(* ################################################################# *)
(** * A Faster [elements] Implementation *)


  Hint Immediate fast_elements_tr_equation_1 : tree_eqns.
  Hint Immediate fast_elements_tr_equation_2 : tree_eqns.

(** The implemention of [elements] is inefficient because of how
    it uses the [++] operator.  On a balanced tree its running time is
    linearithmic, because it does a linear number of concatentations
    at each level of the tree. On an unbalanced tree it's quadratic
    time.  Here's a tail-recursive implementation than runs in linear
    time, regardless of whether the tree is balanced: *)

(** **** Exercise: 3 stars, standard (fast_elements_eq_elements) *)

(** Prove that [fast_elements] and [elements] compute the same
    function. *)

  Lemma app_comm_K_Z : 
    forall (x: list (key * V)) y z, 
      (x ++ y ++ z = (x ++ y) ++ z)%list.
  Proof.
    induction x;
    mirrorsolve.
  Qed.

  Hint Immediate app_comm_K_Z : tree_eqns.

  Lemma fast_elements_tr_helper :
    forall (t : tree) (lst : list (key * V)),
      (fast_elements_tr t lst = elements t ++ lst)%list.
  Proof.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate fast_elements_tr_helper : tree_eqns.

  Lemma app_nil_r_K_V:
    forall (x: list (key * V)), (x ++ [] = x)%list.
  Proof.
    induction x;
    mirrorsolve.
  Qed.

  Hint Immediate app_nil_r_K_V : tree_eqns.

  Hint Immediate fast_elements_equation_1 : tree_eqns.
  Lemma fast_elements_eq_elements : forall (t : tree),
      fast_elements t = elements t.
  Proof.
    mirrorsolve.
  Qed.

  Hint Immediate fast_elements_eq_elements : tree_eqns.


(** [] *)

(** Since the two implementations compute the same function, all
    the results we proved about the correctness of [elements]
    also hold for [fast_elements].  For example: *)

  Corollary fast_elements_correct :
    forall (t: tree) (k : key) (v d : V),
      BST t ->
      In (k, v) (fast_elements t) ->
      bound_t k t = true /\ lookup_t d k t = v.
  Proof.
    mirrorsolve.
  Qed.

(** This corollary illustrates a general technique:  prove the correctness
    of a simple, slow implementation; then prove that the slow version
    is functionally equivalent to a fast implementation.  The proof of
    correctness for the fast implementation then comes "for free". *)

(* ################################################################# *)
(** * An Algebraic Specification of [elements] *)

(** The verification of [elements] we did above did not adhere to the
    algebraic specification approach, which would suggest that we look
    for equations of the form

      elements empty_tree = ...
      elements (insert k v t) = ... (elements t) ...

    The first of these is easy; we can trivially prove the following:
    *)

  Lemma elements_empty :
      elements empty_tree = [].
  Proof.
    mirrorsolve.
  Qed.

(** But for the second equation, we have to express the result of
    inserting [(k, v)] into the elements list for [t], accounting for
    ordering and the possibility that [t] may already contain a pair
    [(k, v')] which must be replaced.  The following rather ugly
    function will do the trick: *)

(** That's not satisfactory, because the definition of
    [kvs_insert] is so complex. Moreover, this equation doesn't tell
    us anything directly about the overall properties of [elements t]
    for a given tree [t].  Nonetheless, we can proceed with a rather
    ugly verification. *)

(* MIRRORSOLVE: We can't do this one because it uses Forall, but we can prove an equivalent version with lt/gt_list. *)

  (** **** Exercise: 3 stars, standard, optional (kvs_insert_split) *)
  Lemma kvs_insert_split :
    forall (v v0 : V) (e1 e2 : list (key * V)) (k k0 : key),
      (Forall (fun '(k',_) => k' < k0) e1 ->
      Forall (fun '(k',_) => k' > k0) e2 ->
      kvs_insert k v (e1 ++ (k0,v0):: e2) =
      if k <? k0 then
        (kvs_insert k v e1) ++ (k0,v0)::e2
      else if k >? k0 then
            e1 ++ (k0,v0)::(kvs_insert k v e2)
          else
            e1 ++ (k,v)::e2)%list.
  Proof.
  (* FILL IN HERE *) Admitted.
  (** [] *)

  Hint Immediate kvs_insert_equation_1 : tree_eqns.
  Hint Immediate kvs_insert_equation_2 : tree_eqns.

  Lemma kvs_insert_split' :
    forall (e1 e2 : list (key * V)) (v v0 : V) (k k0 : key),
      (lt_list k0 e1 -> 
      gt_list k0 e2 ->
      kvs_insert k v (e1 ++ (k0,v0):: e2) =
      ite (k <? k0) 
        ((kvs_insert k v e1) ++ (k0,v0)::e2) (
      ite (k >? k0) 
        (e1 ++ (k0,v0)::(kvs_insert k v e2)) (
        (e1 ++ (k,v)::e2))))%list.
  Proof.
    induction e1;
    induction e2;
    mirrorsolve.
  Qed.

  Hint Immediate kvs_insert_split' : tree_eqns.
  (** **** Exercise: 3 stars, standard, optional (kvs_insert_elements) *)
  Lemma kvs_insert_elements : forall (t : tree),
      BST t ->
      forall (k : key) (v : V),
        elements (insert_t k v t) = kvs_insert k v (elements t).
  Proof.
    induction t;
    mirrorsolve.
  Qed.


(* MIRRORSOLVE: We can't do any of these specs because they use functional maps.
   Although maybe there is a clever way to represent functional maps in SMT.
  *)

(* ################################################################# *)
(** * Model-based Specifications *)

(** At the outset, we mentioned studying two techniques for
    specifying the correctness of BST operations in this chapter.  The
    first was algebraic specification.

    Another approach to proving correctness of search trees is to
    relate them to our existing implementation of functional partial
    maps, as developed in [Maps]. To prove the correctness of a
    search-tree algorithm, we can prove:

    - Any search tree corresponds to some functional partial map,
      using a function or relation that we write down.

    - The [lookup] operation on trees gives the same result as the
      [find] operation on the corresponding map.

    - Given a tree and corresponding map, if we [insert] on the tree
      and [update] the map with the same key and value, the resulting
      tree and map are in correspondence.

    This approach is sometimes called _model-based specification_: we
    show that our implementation of a data type corresponds to a more
    more abstract _model_ type that we already understand. To reason
    about programs that use the implementation, it suffices to reason
    about the behavior of the abstract type, which may be
    significantly easier.  For example, we can take advantage of laws
    that we proved for the abstract type, like [update_eq] for
    functional maps, without having to prove them again for the
    concrete tree type.

    We also need to be careful here, because the type of functional
    maps as defined in [Maps] do not actually behave quite like
    our tree-based maps. For one thing, functional maps can be defined
    on an infinite number of keys, and there is no mechanism for
    enumerating over the key set. To maintain correspondence with our
    finite trees, we need to make sure that we consider only
    functional maps built by finitely many applications of constructor
    functions ([empty] and [update]). Also, thanks to functional
    extensionality, functional maps obey stronger equality laws than
    our trees do (as we investigated in the [direct_equalities]
    exercise above), so we should not be misled into thinking that
    every fact we can prove about abstract maps necessarily holds for
    concrete ones.

    Compared to the algebraic-specification approach described earlier
    in this chapter, the model-based approach can save some proof
    effort, especially if we already have a well-developed theory for
    the abstract model type.  On the other hand, we have to give an
    explicit _abstraction_ relation between trees and maps, and show
    that it is maintained by all operations. In the end, about the
    same amount of work is needed to show correctness, though the work
    shows up in different places depending on how the abstraction
    relation is defined. *)

(** We now give a model-based specification for trees in terms
    of functional partial maps. It is based on a simple abstraction
    relation that builds a functional map element by element. *)

  (* Fixpoint map_of_list {V : Type} (el : list (key * V)) : partial_map V :=
    match el with
    | [] => empty
    | (k, v) :: el' => update (map_of_list el') k v
    end.

  Definition Abs {V : Type} (t : tree V) : partial_map V :=
    map_of_list (elements t). *)

(** In general, model-based specifications may use an abstraction
    relation, allowing each concrete value to be related to multiple
    abstract values.  But in this case a simple abstraction _function_
    will do, assigning a unique abstract value to each concrete
    one. *)

(** One small difference between trees and functional maps is that
    applying the latter returns an [option V] which might be [None],
    whereas [lookup] returns a default value if key is not bound
    lookup fails.  We can easily provide a function on functional
    partial maps having the latter behavior. *)

(* Definition find {V : Type} (d : V) (k : key) (m : partial_map V) : V :=
  match m k with
  | Some v => v
  | None => d
  end. *)

(** We also need a [bound] operation on maps. *)

(* Definition map_bound {V : Type} (k : key) (m : partial_map V) : bool :=
  match m k with
  | Some _ => true
  | None => false
  end. *)

(** We now proceed to prove that each operation preserves (or establishes)
    the abstraction relationship in an appropriate way:

    concrete        abstract
    --------        --------
    empty_tree      empty
    bound           map_bound
    lookup          find
    insert          update
*)

(** The following lemmas will be useful, though you are not required
    to prove them. They can all be proved by induction on the list. *)

(** **** Exercise: 2 stars, standard, optional (in_fst) *)
(* Lemma in_fst : forall (X Y : Type) (lst : list (X * Y)) (x : X) (y : Y),
    In (x, y) lst -> In x (map fst lst).
Proof. *)
  (* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars, standard, optional (in_map_of_list) *)
(* Lemma in_map_of_list : forall (V : Type) (el : list (key * V)) (k : key) (v : V),
    NoDup (map fst el) ->
    In (k,v) el -> (map_of_list el) k = Some v.
Proof. *)
(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars, standard, optional (not_in_map_of_list) *)
(* Lemma not_in_map_of_list : forall (V : Type) (el : list (key * V)) (k : key),
    ~ In k (map fst el) -> (map_of_list el) k = None.
Proof. *)
  (* FILL IN HERE *)
(** [] *)

(* Lemma empty_relate : forall (V : Type),
    @Abs V empty_tree = empty.
Proof.
  reflexivity.
Qed. *)

(** **** Exercise: 3 stars, standard, optional (bound_relate) *)

(* Theorem bound_relate : forall (V : Type) (t : tree V) (k : key),
    BST t ->
    map_bound k (Abs t) = bound k t.
Proof. *)
  (* FILL IN HERE *)

(** [] *)

(** **** Exercise: 3 stars, standard, optional (lookup_relate) *)

(* Lemma lookup_relate : forall (V : Type) (t : tree V) (d : V) (k : key),
    BST t -> find d k (Abs t) = lookup d k t.
Proof. *)
  (* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, standard, optional (insert_relate) *)
(*
Lemma insert_relate : forall (V : Type) (t : tree V) (k : key) (v : V),
  BST t -> Abs (insert k v t) = update (Abs t) k v.
Proof.
  (* TODO: find a direct proof that doesn't rely on [kvs_insert_elements] *)
    unfold Abs.
  intros.
  rewrite kvs_insert_elements; auto.
  remember (elements t) as l.
  clear -l. 
  (* clear everything not about [l] *)
  (* Hint: proceed by induction on [l]. *)
    (* FILL IN HERE *)
    *)
(** [] *)

(** The previous three lemmas are in essence saying that the following
    diagrams commute.

             bound k
      t -------------------+
      |                    |
  Abs |                    |
      V                    V
      m -----------------> b
           map_bound k

            lookup d k
      t -----------------> v
      |                    |
  Abs |                    | Some
      V                    V
      m -----------------> Some v
             find d k

            insert k v
      t -----------------> t'
      |                    |
  Abs |                    | Abs
      V                    V
      m -----------------> m'
            update' k v

    Where we define:

      update' k v m = update m k v

*)

(** Functional partial maps lack a way to extract or iterate
    over their elements, so we cannot give an analogous abstract
    operation for [elements]. Instead, we can prove this trivial
    little lemma. *)

(* Lemma elements_relate : forall (V : Type) (t : tree V),
  BST t ->
  map_of_list (elements t) = Abs t.
Proof.
  unfold Abs. intros. reflexivity.
Qed. *)

(* ################################################################# *)
(** * An Alternative Abstraction Relation (Optional, Advanced) *)

(** There is often more than one way to specify a suitable abstraction
    relation between given concrete and abstract datatypes. The
    following exercises explore another way to relate search trees to
    functional partial maps without using [elements] as an
    intermediate step.

    We extend our definition of functional partial maps by adding a
    new primitive for combining two partial maps, which we call
    [union].  Our intention is that it only be used to combine maps
    with disjoint key sets; to keep the operation symmetric, we make
    the result be undefined on any key they have in common.  *)

(* Definition union {X} (m1 m2: partial_map X) : partial_map X :=
  fun k =>
    match (m1 k, m2 k) with
    | (None, None) => None
    | (None, Some v) => Some v
    | (Some v, None) => Some v
    | (Some _, Some _) => None
    end. *)

(** We can prove some simple properties of lookup and update on unions,
    which will prove useful later. *)

(** **** Exercise: 2 stars, standard, optional (union_collapse) *)
(* Lemma union_left : forall {X} (m1 m2: partial_map X) k,
    m2 k = None -> union m1 m2 k = m1 k.
Proof. 
(* FILL IN HERE *) *)

(* Lemma union_right : forall {X} (m1 m2: partial_map X) k,
    m1 k = None ->
    union m1 m2 k = m2 k.
Proof.
(* FILL IN HERE *) *)

(* Lemma union_both : forall {X} (m1 m2 : partial_map X) k v1 v2,
    m1 k = Some v1 ->
    m2 k = Some v2 ->
    union m1 m2 k = None.
Proof.
(* FILL IN HERE *) *)
(** [] *)

(** **** Exercise: 3 stars, standard, optional (union_update) *)
(* Lemma union_update_right : forall {X} (m1 m2: partial_map X) k v,
    m1 k = None ->
    update (union m1 m2) k v = union m1 (update m2 k v).
Proof.
(* FILL IN HERE *) *)

(* Lemma union_update_left : forall {X} (m1 m2: partial_map X) k v,
    m2 k = None ->
    update (union m1 m2) k v = union (update m1 k v) m2.
Proof.
(* FILL IN HERE *) *)
(** [] *)

(** We can now write a direct conversion function from trees to maps
    based on the structure of the tree, and prove a basic property
    preservation result. *)

(* Fixpoint map_of_tree {V : Type} (t: tree V) : partial_map V :=
  match t with
  | E => empty
  | T l k v r => update (union (map_of_tree l) (map_of_tree r)) k v
  end. *)

(** **** Exercise: 3 stars, advanced, optional (map_of_tree_prop) *)
(* Lemma map_of_tree_prop : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
    ForallT P t ->
    forall k v, (map_of_tree t) k = Some v ->
           P k v.
Proof.
  (* FILL IN HERE *) *)
(** [] *)

(** Finally, we define our new abstraction function, and prove the
    same lemmas as before. *)

(* Definition Abs' {V : Type} (t: tree V) : partial_map V :=
  map_of_tree t.

Lemma empty_relate' : forall (V : Type),
    @Abs' V empty_tree = empty.
Proof.
  reflexivity.
Qed. *)

(** **** Exercise: 3 stars, advanced, optional (bound_relate') *)
(* Theorem bound_relate' : forall (V : Type) (t : tree V) (k : key),
    BST t ->
    map_bound k (Abs' t) = bound k t.
Proof.
  (* FILL IN HERE *) *)
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (lookup_relate') *)
(* Lemma lookup_relate' : forall (V : Type) (d : V) (t : tree V) (k : key),
    BST t -> find d k (Abs' t) = lookup d k t.
Proof.
  (* FILL IN HERE *) *)
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (insert_relate') *)
(* Lemma insert_relate' : forall (V : Type) (k : key) (v : V) (t : tree V),
   BST t -> Abs' (insert k v t) = update (Abs' t) k v.
Proof.
  (* FILL IN HERE *) *)
(** [] *)

(** The [elements_relate] lemma, which was trivial for our previous [Abs]
    function, is considerably harder this time.  We suggest starting with
    an auxiliary lemma. *)

(** **** Exercise: 3 stars, advanced, optional (map_of_list_app) *)
(* Lemma map_of_list_app : forall (V : Type) (el1 el2: list (key * V)),
   disjoint (map fst el1) (map fst el2) ->
   map_of_list (el1 ++ el2) = union (map_of_list el1) (map_of_list el2).
Proof.
  (* FILL IN HERE *) *)
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (elements_relate') *)
(* Lemma elements_relate' : forall (V : Type) (t : tree V),
  BST t ->
  map_of_list (elements t) = Abs' t.
Proof.
  (* FILL IN HERE *) *)
(** [] *)

(* ################################################################# *)
(** * Efficiency of Search Trees *)

(** All the theory we've developed so far has been about correctness.
    But the reason we use binary search trees is that they are
    efficient.  That is, if there are [N] elements in a (reasonably
    well balanced) BST, each insertion or lookup takes about [log N]
    time.

    What could go wrong?

     1. The search tree might not be balanced.  In that case, each
        insertion or lookup will take as much as linear time.

        - SOLUTION: use an algorithm that ensures the trees stay
          balanced.  We'll do that in [Redblack].

     2. Our keys are natural numbers, and Coq's [nat] type takes linear
        time per comparison.  That is, computing (j <? k) takes time
        proportional to the value of [k-j].

        - SOLUTION: represent keys by a data type that has a more
          efficient comparison operator.  We used [nat] in this chapter
          because it's something easy to work with.

     3. There's no notion of running time in Coq.  That is, we can't
        say what it means that a Coq function "takes N steps to
        evaluate."  Therefore, we can't prove that binary search trees
        are efficient.

        - SOLUTION 1: Don't prove (in Coq) that they're efficient;
          just prove that they are correct.  Prove things about their
          efficiency the old-fashioned way, on pencil and paper.

        - SOLUTION 2: Prove in Coq some facts about the height of the
          trees, which have direct bearing on their efficiency.  We'll
          explore that in [Redblack].

        - SOLUTION 3: Apply bleeding-edge frameworks for reasoning
          about run-time of programs represented in Coq.

      4. Our functions in Coq are models of implementations in "real"
         programming languages.  What if the real implementations
         differ from the Coq models?

         - SOLUTION: Use Coq's [extraction] feature to derive the real
	   implementation (in Ocaml or Haskell) automatically from the
	   Coq function.  Or, use Coq's [Compute] or [Eval
	   native_compute] feature to compile and run the programs
	   efficiently inside Coq.  We'll explore [extraction] in a
	   [Extract]. *)

(* 2021-08-11 15:15 *)

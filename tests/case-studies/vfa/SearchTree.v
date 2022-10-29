
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
Require Import MirrorSolve.Automation.Equations.
From Hammer Require Import Hammer.

Require Import MirrorSolve.Crush.

Ltac hammer' := timeout 60 hammer.
Ltac crush' := timeout 60 crush.

Inductive sorted : list Z -> Prop :=
  | sorted_nil : sorted []
  | sorted_1 : forall x, sorted [x]
  | sorted_cons : forall x y l,
    (x <= y)%Z -> sorted (y :: l) -> sorted (x :: y :: l).

Hint Constructors sorted.

(*** MS EFFORT {"type": "definition"} *)
Fixpoint NoDup_Z (xs: list Z) := 
  match xs with 
  | [] => True
  | x' :: xs' => 
    ~ In x' xs' /\ NoDup_Z xs'
  end.

MetaCoq Run (infer_equations NoDup_Z).

Definition disjoint (l1 l2: list Z) := forall (x : Z),
  In x l1 -> ~ In x l2.

(*** MS EFFORT {"type": "lemma"} *)
Lemma disjoint_spec:
  forall l1 l2, disjoint l1 l2 <-> (forall x, In x l1 -> ~ In x l2).
Proof.
  intuition eauto.
Qed.

Section SearchTree.
  Variable (V: Type).
  Notation key := Z.

  Definition app_key := Eval compute in @List.app key.
  Definition app_key_V := Eval compute in @List.app (key * V).
  Definition In_key := Eval compute in  @List.In key.
  Definition In_key_V := Eval compute in @List.In (key * V).

(** [E] represents the empty map.  [T l k v r] represents the
    map that binds [k] to [v], along with all the bindings in [l] and
    [r].  No key may be bound more than once in the map. *)

  Inductive tree : Type :=
    | E
    | T (l : tree) (k : key) (v : V) (r : tree).

  Hint Constructors tree.

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

  (*** MS EFFORT {"type": "definition"} *)
  Fixpoint lt_t (k: Z) (t: tree) : Prop := 
    match t with 
    | E => True
    | T l k' _ r => k' < k /\ lt_t k l /\ lt_t k r
    end. 

  Lemma lt_t_spec : forall x t, ForallT (fun y _ => y < x) t <-> lt_t x t.
  Proof.
    induction t; simpl in *; intuition eauto.
  Qed.

  (*** MS EFFORT {"type": "definition"} *)
  Fixpoint lt_list (k: Z) (t: list (key * V)) : Prop := 
    match t with 
    | [] => True
    | (k', _) :: t' => k' < k /\ lt_list k t'
    end. 

  (*** MS EFFORT {"type": "definition"} *)
  Fixpoint lt_list_s (k: key) (t: list key) : Prop := 
    match t with 
    | [] => True
    | k' :: t' => k' < k /\ lt_list_s k t'
    end. 

  (*** MS EFFORT {"type": "definition"} *)
  Fixpoint gt_t (k: Z) (t: tree) : Prop := 
    match t with 
    | E => True
    | T l k' _ r => k' > k /\ gt_t k l /\ gt_t k r
    end. 
  
  
  Lemma gt_t_spec : forall x t, ForallT (fun y _ => y > x) t <-> gt_t x t.
  Proof.
    induction t; simpl in *; intuition eauto.
  Qed.

  (*** MS EFFORT {"type": "definition"} *)
  Fixpoint gt_list (k: Z) (t: list (key * V)) : Prop := 
    match t with 
    | [] => True
    | (k', _) :: t' => k' > k /\ gt_list k t'
    end. 
  (*** MS EFFORT {"type": "definition"} *)
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

  Hint Constructors BST.

  (*** MS EFFORT {"type": "definition"} *)
  Fixpoint ordered (t: tree) : Prop :=
    match t with 
    | E => True
    | T l k _ r => 
      lt_t k l /\ 
      gt_t k r /\ 
      ordered l /\ ordered r
    end.

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 0, "hammer": 1, "crush": 1} *)
  Lemma ordered_spec : 
    forall t, BST t <-> ordered t.
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t.
    - crush'.
    - crush'.
      admit.
    Restart.
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

  (*** MS EFFORT {"type": "definition"} *)
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
    ; pack app_key
    ; pack app_key_V
  ])%type.

  Unset Universe Polymorphism.

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
      ; pack In_key
      ; pack In_key_V
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
    timeout 60 (prep_proof;
    quote_reflect_tree;
    check_goal_unsat).

  Set MirrorSolve Solver "z3".

  Hint Immediate ordered_spec : tree_eqns. 

  MetaCoq Run (infer_equations ordered).

  Hint Immediate ordered_equation_1 : tree_eqns. 
  Hint Immediate ordered_equation_2 : tree_eqns. 
    

(** **** Exercise: 1 star, standard (empty_tree_BST) *)

(** Prove that the empty tree is a BST. *)

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": False, "ho": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 1} *)
  Theorem empty_tree_BST : 
      BST E.
  Proof.
    try crush'.
    Restart.
    try hammer'.
    Restart.
    mirrorsolve.
  Qed.

(** [] *)

(** **** Exercise: 4 stars, standard (insert_BST) *)

(** Prove that [insert] produces a BST, assuming it is given one.

    Start by proving this helper lemma, which says that [insert]
    preserves any node predicate. Proceed by induction on [t]. *)

  (* first, reflect lt_t and gt_t: *)

  MetaCoq Run (infer_equations lt_t).

  Hint Immediate lt_t_equation_1 : tree_eqns. 
  Hint Immediate lt_t_equation_2 : tree_eqns. 

  MetaCoq Run (infer_equations gt_t).

  Hint Immediate gt_t_equation_1 : tree_eqns. 
  Hint Immediate gt_t_equation_2 : tree_eqns. 

  Hint Immediate insert_t_equation_1 : tree_eqns.
  Hint Immediate insert_t_equation_2 : tree_eqns.


  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 2, "crush": 2} *)
  Lemma gt_t_trans : 
    forall (x y : Z), 
      x > y -> 
      forall t, gt_t x t -> gt_t y t.
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    mirrorsolve.
  Qed.

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 2, "crush": 2} *)
  Lemma lt_t_trans : 
    forall (x y : Z), 
      x < y -> 
      forall t, lt_t x t -> lt_t y t.
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate lt_t_trans : tree_eqns.
  Hint Resolve lt_t_trans.
  Hint Immediate gt_t_trans : tree_eqns.
  Hint Resolve gt_t_trans.

  Hint Immediate Z.ltb_lt : tree_eqns.

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 0} *)
  Lemma lt_t_insert : 
    forall t x k, 
      lt_t x t->
      k < x -> 
      forall v, 
        lt_t x (insert_t k v t).
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate lt_t_insert : tree_eqns.
  Hint Resolve lt_t_insert.

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 2, "crush": 0} *)
  Lemma gt_t_insert : 
    forall t x k, 
      gt_t x t->
      k > x -> 
      forall v, 
        gt_t x (insert_t k v t).
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    mirrorsolve.
  Qed.
  Hint Immediate gt_t_insert : tree_eqns.
  Hint Resolve gt_t_insert.

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 0} *)
  Lemma ordered_insert : 
    forall t x k, 
      ordered t -> ordered (insert_t k x t).
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    mirrorsolve.
  Qed.
  Hint Immediate ordered_insert : tree_eqns.
  Hint Resolve ordered_insert.


(** Now prove the main theorem. Proceed by induction on the evidence
    that [t] is a BST. *)

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": False, "ho": False, "goals": 2, "ms": 2, "hammer": 2, "crush": 0} *)
  Theorem insert_BST : forall (k : key) (v : V) (t : tree),
      BST t -> BST (insert_t k v t).
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    mirrorsolve.
  Qed.
  Hint Immediate insert_BST : tree_eqns.
  Hint Resolve insert_BST.

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


  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 1} *)
  Theorem lookup_empty : forall (d : V) (k : key),
      lookup_t d k empty_tree = d.
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
    mirrorsolve.
  Qed.

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 2, "ms": 2, "hammer": 0, "crush": 0} *)
  Theorem lookup_insert_eq : forall (t : tree) (d : V) (k : key) (v : V),
      lookup_t d k (insert_t k v t)  = v.
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t; 
    mirrorsolve.
  Qed.

  Hint Immediate lookup_insert_eq : tree_eqns.
  Hint Immediate lookup_empty : tree_eqns.
  Hint Resolve lookup_insert_eq.
  Hint Resolve lookup_empty.


(** The basic method of that proof is to repeatedly [bdestruct]
    everything in sight, followed by generous use of [lia] and
    [auto]. Let's automate that. *)


(** The tactic immediately pays off in proving the third
    equation. *)

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 2, "ms": 2, "hammer": 0, "crush": 0} *)
  Theorem lookup_insert_neq :
    forall (t : tree) (d : V) (k k' : key) (v : V),
    k <> k' -> lookup_t d k' (insert_t k v t) = lookup_t d k' t.
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate lookup_insert_neq : tree_eqns.
  Hint Resolve lookup_insert_neq.

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

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 2, "ms": 2, "hammer": 2, "crush": 1} *)
  Theorem bound_default :
    forall (t: tree) (k : key) (d : V),
      bound_t k t = false ->
      lookup_t d k t = d.
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate bound_default : tree_eqns.
  Hint Resolve bound_default.

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

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 2, "ms": 2, "hammer": 0, "crush": 0} *)
  Lemma lookup_insert_shadow :
    forall (t : tree) (v v' d: V) (k k' : key),
      lookup_t d k' (insert_t k v (insert_t k v' t)) = lookup_t d k' (insert_t k v t).
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    mirrorsolve.
  Qed.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (lookup_insert_same) *)

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 2, "ms": 2, "hammer": 0, "crush": 0} *)
  Lemma lookup_insert_same :
    forall (t : tree) (k k' : key) (d : V),
      lookup_t d k' (insert_t k (lookup_t d k t) t) = lookup_t d k' t.
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t; 
    mirrorsolve.
  Qed.

  Hint Immediate lookup_insert_same : tree_eqns.
  Hint Resolve lookup_insert_same.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (lookup_insert_permute) *)

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 2, "ms": 2, "hammer": 0, "crush": 0} *)
  Lemma lookup_insert_permute :
    forall (t: tree) (v1 v2 d : V) (k1 k2 k': key),
      k1 <> k2 ->
      lookup_t d k' (insert_t k1 v1 (insert_t k2 v2 t))
      = lookup_t d k' (insert_t k2 v2 (insert_t k1 v1 t)).
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t; 
    mirrorsolve.
  Qed.

  Hint Immediate lookup_insert_permute : tree_eqns.
  Hint Resolve lookup_insert_permute.
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

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 2, "ms": 2, "hammer": 0, "crush": 0} *)
  Lemma insert_shadow_equality : forall (t : tree) (k : key) (v v' : V),
      insert_t k v (insert_t k v' t) = insert_t k v t.
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t; 
    mirrorsolve.
  Qed.

  Hint Immediate insert_shadow_equality : tree_eqns.
  Hint Resolve insert_shadow_equality.

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

  MetaCoq Run (infer_equations In_key_V).

  Hint Immediate In_key_V_equation_1 : tree_eqns.
  Hint Immediate In_key_V_equation_2 : tree_eqns.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma In_key_V_spec : 
    forall x xs, 
      In_key_V x xs <-> In x xs.
  Proof.
    intros; eapply iff_refl.
  Qed.

  Hint Immediate In_key_V_spec : tree_eqns.
  Hint Resolve In_key_V_spec.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma in_app_iff' :  
    forall l l' (a:(key * V)), In a (l++l') <-> In a l \/ In a l'.
  Proof.
    eapply in_app_iff.
  Qed.

  Hint Immediate in_app_iff' : tree_eqns.
  Hint Resolve in_app_iff'.

  
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 1} *)
  Theorem elements_complete : 
    forall (t: tree) (k : key) (v d : V),
      bound_t k t = true ->
      lookup_t d k t = v ->
      In (k, v) (elements t).
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate elements_complete : tree_eqns.
  Hint Resolve elements_complete.

(** [] *)

(** Proving correctness requires more work than completeness.

    [BST] uses [ForallT] to say that all nodes in the left/right
    subtree have smaller/greater keys than the root.  We need to
    relate [ForallT], which expresses that all nodes satisfy a
    property, to [Forall], which expresses that all list elements
    satisfy a property.

    The standard library contains a helpful lemma about [Forall]: *)

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

  (* MetaCoq Run (infer_equations lt_list). *)
  (* MetaCoq Run (infer_equations gt_list). *)

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma lt_list_equation_1 : forall k, lt_list k [] <-> True. 
  Proof. intros; eapply iff_refl. Qed.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma lt_list_equation_2 : forall k k' x t', lt_list k ((k', x) :: t') <-> k' < k /\ lt_list k t'. 
  Proof. intros. eapply iff_refl. Qed.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma gt_list_equation_1 : forall k, gt_list k [] <-> True. 
  Proof. intros; eapply iff_refl. Qed.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma gt_list_equation_2 : forall k k' x t', gt_list k ((k', x) :: t') <-> k' > k /\ gt_list k t'. 
  Proof. intros. eapply iff_refl. Qed.

  Hint Immediate lt_list_equation_1 : tree_eqns.
  Hint Immediate lt_list_equation_2 : tree_eqns.
  Hint Immediate gt_list_equation_1 : tree_eqns.
  Hint Immediate gt_list_equation_2 : tree_eqns.

  (* However, we can prove that it preserves lt_t and gt_t, as well as that lt_list and gt_list are transitive *)

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 2, "crush": 2} *)
  Lemma lt_list_trans : 
    forall l x y,
      x < y -> 
      lt_list x l -> 
      lt_list y l.
  Proof.
    induction l;
    try hammer'.
    Restart.
    induction l;
    try crush'.
    Restart.
    induction l;
    mirrorsolve.
  Qed.

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 2, "crush": 2} *)
  Lemma gt_list_trans : 
    forall l x y,
      x > y -> 
      gt_list x l -> 
      gt_list y l.
  Proof.
    induction l;
    try hammer'.
    Restart.
    induction l;
    try crush'.
    Restart.
    induction l;
    mirrorsolve.
  Qed.

  Hint Immediate lt_list_trans : tree_eqns.
  Hint Immediate gt_list_trans : tree_eqns.
  Hint Resolve lt_list_trans.
  Hint Resolve gt_list_trans.

  Set MirrorSolve Solver "z3".

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 2, "crush": 2} *)
  Lemma lt_list_In : 
    forall x l, 
      lt_list x l <-> (forall y v, In (y, v) l -> y < x).
  Proof.
    induction l;
    try hammer'.
    Restart.
    induction l;
    try crush'.
    Restart.
    induction l;
    mirrorsolve.
  Qed.

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 2, "crush": 2} *)
  Lemma gt_list_In : 
    forall x l, 
      gt_list x l <-> (forall y v, In (y, v) l -> y > x).
  Proof.
    induction l;
    try hammer'.
    Restart.
    induction l;
    try crush'.
    Restart.
    induction l;
    mirrorsolve.
  Qed.

  Hint Immediate lt_list_In : tree_eqns.
  Hint Immediate gt_list_In : tree_eqns.

  Hint Resolve lt_list_In.
  Hint Resolve gt_list_In.


  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 0} *)
  Lemma lt_t_elements : 
    forall t x,
      lt_t x t <-> lt_list x (elements t).
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    try mirrorsolve.
  Qed.

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 0} *)
  Lemma gt_t_elements : 
    forall t x,
      gt_t x t <-> gt_list x (elements t).
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    try mirrorsolve.
  Qed.

  Hint Immediate lt_t_elements : tree_eqns.
  Hint Immediate gt_t_elements : tree_eqns.

  Hint Resolve lt_t_elements.
  Hint Resolve gt_t_elements.


(** [] *)

(** **** Exercise: 4 stars, standard (elements_correct) *)

(** Prove that [elements] is correct. Proceed by induction on the
    evidence that [t] is a BST. *)

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": False, "ho": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 0} *)
  Theorem elements_correct : 
    forall (t : tree) (k : key) (v d : V),
      BST t ->
      In (k, v) (elements t) ->
      bound_t k t = true /\ lookup_t d k t = v.
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate elements_correct : tree_eqns.
  Hint Resolve elements_correct.

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

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": False, "ho": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 1} *)
  Theorem elements_complete_inverse :
    forall (t : tree) (k : key) (v : V) ,
      BST t -> 
      bound_t k t = false ->
      ~ In (k, v) (elements t).
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate elements_complete_inverse : tree_eqns.
  Hint Resolve elements_complete_inverse.

(** [] *)

(** Prove the main result.  You don't need induction. *)

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 1} *)
  Theorem elements_correct_inverse :
    forall (t : tree) (k : key) ,
      (forall v, ~ In (k, v) (elements t)) ->
      bound_t k t = false.
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate elements_correct_inverse : tree_eqns.
  Hint Resolve elements_correct_inverse.

  
(* ================================================================= *)
(** ** Part 2: Sorted (Advanced) *)

(** We want to show that [elements] is sorted by keys.  We follow a
    proof technique contributed by Lydia Symmons et al.*)

(** **** Exercise: 3 stars, advanced (sorted_app) *)

  (* First we reflect the definition of sorted to UF: *)

  (* MetaCoq Run (infer_equations sorted). *)

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma sorted_nil' : 
    sorted [] <-> True.
  Proof.
    intros;
    simpl;
    intuition eauto.
  Qed.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma sorted_one' :
    forall x, 
    sorted [x] <-> True.
  Proof.
    intros;
    simpl;
    intuition eauto.
  Qed.

  (*** MS EFFORT {"type": "lemma"} *)
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
  Qed.

  Hint Immediate sorted_nil' : tree_eqns.
  Hint Immediate sorted_one' : tree_eqns.
  Hint Immediate sorted_cons' : tree_eqns.

  MetaCoq Run (infer_equations lt_list_s).

  Hint Immediate lt_list_s_equation_1 : tree_eqns.
  Hint Immediate lt_list_s_equation_2 : tree_eqns.

  MetaCoq Run (infer_equations app_key).

  Hint Immediate app_key_equation_1 : tree_eqns.
  Hint Immediate app_key_equation_2 : tree_eqns.
  
  (*** MS EFFORT {"type": "lemma"} *)
  Lemma app_key_spec : 
    forall x y, (x ++ y = app_key x y)%list.
  Proof.
    intros; eapply eq_refl.
  Qed.

  Hint Immediate app_key_spec : tree_eqns.

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 1} *)
  Lemma sorted_lt_end : 
    forall l x, 
      lt_list_s x l -> 
      sorted l -> 
      sorted (l ++ [x]).
  Proof.
    induction l;
    try hammer'.
    Restart.
    induction l;
    try crush'.
    Restart.
    induction l;
    try mirrorsolve.
  Qed.

  Hint Immediate sorted_lt_end : tree_eqns.
  Hint Resolve sorted_lt_end.

  MetaCoq Run (infer_equations gt_list_s).

  Hint Immediate gt_list_s_equation_1 : tree_eqns.
  Hint Immediate gt_list_s_equation_2 : tree_eqns.

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 2} *)
  Lemma sorted_gt_beginning : 
    forall r x, 
      gt_list_s x r -> 
      sorted r -> 
      sorted (x :: r).
  Proof.
    induction r;
    try hammer'.
    Restart.
    induction r;
    try crush'.
    Restart.
    induction r;
    mirrorsolve.
  Qed.

  Hint Immediate sorted_gt_beginning : tree_eqns.
  Hint Resolve sorted_gt_beginning.

(** Prove that inserting an intermediate value between two lists
    maintains sortedness. Proceed by induction on the evidence
    that [l1] is sorted. *)

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": False, "goals": 4, "ms": 4, "hammer": 2, "crush": 2} *)
  Lemma sorted_app': forall l1 l2 x,
    sorted l1 -> sorted l2 ->
    lt_list_s x l1 -> gt_list_s x l2 ->
   sorted (l1 ++ x :: l2).
  Proof.
    induction l1;
    induction l2;
    try hammer'.
    Restart.
    induction l1;
    induction l2.
    - try crush';
      admit.
    - try crush';
      admit.
    - try crush';
      admit.
    - try crush';
      admit.
    Restart.
    induction l1;
    induction l2;
    mirrorsolve.
  Qed.

  Hint Immediate sorted_app' : tree_eqns.
  Hint Resolve sorted_app'.

(** [] *)

(** **** Exercise: 4 stars, advanced (sorted_elements) *)

(** The keys in an association list are the first elements of every
    pair: *)

  Definition list_keys (lst : list (key * V)) :=
    map fst lst.

(** Prove that [elements t] is sorted by keys. Proceed by induction
    on the evidence that [t] is a BST. *)


  Hint Immediate map_fst_equation_1 : tree_eqns.
  Hint Immediate map_fst_equation_2 : tree_eqns.

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 2, "crush": 1} *)
  Lemma map_fst_lts : 
    forall l x, 
      lt_list x l <-> lt_list_s x (map_fst l).
  Proof.
    induction l;
    try hammer'.
    Restart.
    induction l;
    try crush'.
    Restart.
    induction l;
    mirrorsolve. 
  Qed.

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 2, "crush": 1} *)
  Lemma map_fst_gts : 
    forall l x, 
      gt_list x l <-> gt_list_s x (map_fst l).
  Proof.
    induction l;
    try hammer'.
    Restart.
    induction l;
    try crush'.
    Restart.
    induction l;
    mirrorsolve. 
  Qed.

  Hint Immediate map_fst_lts : tree_eqns.
  Hint Immediate map_fst_gts : tree_eqns.
  Hint Resolve map_fst_lts.
  Hint Resolve map_fst_gts.

  MetaCoq Run (infer_equations app_key_V).

  Hint Immediate app_key_V_equation_1 : tree_eqns.
  Hint Immediate app_key_V_equation_2 : tree_eqns.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma app_key_V_spec : 
    forall x y, (x ++ y = app_key_V x y)%list.
  Proof.
    intros; eapply eq_refl.
  Qed.

  Hint Immediate app_key_V_spec : tree_eqns.

  Set MirrorSolve Solver "cvc5".

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 2, "crush": 1} *)
  Lemma map_fst_app :
    forall x y, 
      (map_fst (x ++ y) = map_fst x ++ map_fst y)%list.
  Proof.
    induction x;
    try hammer'.
    Restart.
    induction x;
    try crush'.
    Restart.
    induction x; 
    mirrorsolve.
  Qed. 

  Hint Immediate map_fst_app : tree_eqns.
  Hint Resolve map_fst_app.

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 1} *)
  Theorem sorted_elements' : forall (t : tree),
      BST t -> sorted (map_fst (elements t)).
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    mirrorsolve.
  Qed.

  Hint Resolve sorted_elements' : tree_eqns.
  Hint Resolve sorted_elements'.

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
  Hint Immediate NoDup_Z_equation_1 : tree_eqns.
  Hint Immediate NoDup_Z_equation_2 : tree_eqns.

  MetaCoq Run (infer_equations In_key).

  Hint Immediate In_key_equation_1 : tree_eqns.
  Hint Immediate In_key_equation_2 : tree_eqns.

  (*** MS EFFORT {"type": "lemma"} *)
  Lemma In_key_spec : 
    forall x xs, 
      In_key x xs <-> In x xs.
  Proof.
    intros; eapply iff_refl.
  Qed.

  Hint Immediate In_key_spec : tree_eqns.


(** **** Exercise: 3 stars, advanced, optional (NoDup_append) *)

(** Prove that if two lists are disjoint, appending them preserves
    [NoDup].  Hint: You might already have proved this theorem in an
    advanced exercise in [IndProp]. *)

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 2, "crush": 0} *)
  Lemma disjoint_cons: 
    forall x l r, 
      disjoint (x :: l) r -> disjoint l r.
  Proof.
    induction l;
    try hammer'.
    Restart.
    induction l;
    try crush'.
    Restart.
    induction l;
    mirrorsolve.
  Qed.
  
  Hint Immediate disjoint_cons : tree_eqns.
  Hint Resolve disjoint_cons.

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 2, "crush": 1} *)
  Lemma neg_In_app : 
    forall (x: Z) l r, 
      ~ In x l -> ~ In x r -> ~ In x (l ++ r).
  Proof.
    induction l;
    try hammer'.
    Restart.
    induction l;
    try crush'.
    Restart.
    induction l;
    mirrorsolve.
  Qed.

  Hint Immediate neg_In_app : tree_eqns.
  Hint Resolve neg_In_app.

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 1} *)
  Lemma NoDup_append : forall (l1 l2: list Z),
    NoDup_Z l1 -> NoDup_Z l2 -> disjoint l1 l2 ->
    NoDup_Z (l1 ++ l2).
  Proof.
    induction l1;
    try hammer'.
    Restart.
    induction l1;
    try crush'.
    Restart.
    induction l1;
    mirrorsolve.
  Qed.

  Hint Immediate NoDup_append : tree_eqns.
  Hint Resolve NoDup_append.

  (*** MS LEMMA {"original": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 1} *)
  Lemma Not_In_nil : 
    forall (x: key), ~ In x [].
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
    mirrorsolve.
  Qed.

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 2, "crush": 2} *)
  Lemma Not_In_cons:
    forall l (x: key) x', 
      ~ In x (x' :: l) <-> (x <> x' /\ ~ In x l).
  Proof.
    induction l;
    try hammer'.
    Restart.
    induction l;
    try crush'.
    Restart.
    induction l;
    mirrorsolve.
  Qed.

  Hint Immediate Not_In_nil : tree_eqns.
  Hint Immediate Not_In_cons : tree_eqns.
  Hint Resolve Not_In_nil.
  Hint Resolve Not_In_cons.

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 2} *)
  Lemma gt_t_notin : 
    forall l x, 
      gt_list_s x l -> ~ In x l.
  Proof.
    induction l;
    try hammer'.
    Restart.
    induction l;
    try crush'.
    Restart.
    induction l;
    mirrorsolve.
  Qed.

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 2} *)
  Lemma lt_t_notin : 
    forall l x, 
      lt_list_s x l -> ~ In x l.
  Proof.
    induction l;
    try hammer'.
    Restart.
    induction l;
    try crush'.
    Restart.
    induction l;
    mirrorsolve.
  Qed.

  Hint Immediate gt_t_notin : tree_eqns.
  Hint Immediate lt_t_notin : tree_eqns.
  Hint Resolve gt_t_notin.
  Hint Resolve lt_t_notin.

  (*** MS LEMMA {"original": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 0} *)
  Lemma gt_t_disjoint : 
    forall l2 l1, 
      (forall x, In x l1 -> 
      gt_list_s x l2) -> 
      disjoint l1 l2.
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
    mirrorsolve.
  Qed.

  (*** MS LEMMA {"original": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 0} *)
  Lemma lt_t_disjoint : 
    forall l2 l1, 
      (forall x, In x l1 -> 
      lt_list_s x l2) -> 
      disjoint l1 l2.
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
    mirrorsolve.
  Qed.
  
  Hint Immediate lt_t_disjoint : tree_eqns.
  Hint Immediate gt_t_disjoint : tree_eqns.
  Hint Resolve lt_t_disjoint.
  Hint Resolve gt_t_disjoint.

(** [] *)

(** **** Exercise: 4 stars, advanced, optional (elements_nodup_keys) *)

(** Prove that there are no duplicate keys in the list returned
    by [elements]. Proceed by induction on the evidence that [t] is a
    BST. Make use of library theorems about [map] as needed. *)

(*** MS EFFORT {"type": "edit"} *)
(*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 1} *)
  Theorem elements_nodup_keys' : forall (t : tree),
    ordered t ->
    NoDup_Z (map_fst (elements t)).
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate elements_nodup_keys' : tree_eqns.
  Hint Resolve elements_nodup_keys'.

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

  (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 2, "crush": 2} *)
  Lemma app_comm_K_Z : 
    forall (x: list (key * V)) y z, 
      (x ++ y ++ z = (x ++ y) ++ z)%list.
  Proof.
    induction x;
    try hammer'.
    Restart.
    induction x;
    try crush'.
    Restart.
    induction x;
    mirrorsolve.
  Qed.

  Hint Immediate app_comm_K_Z : tree_eqns.
  Hint Resolve app_comm_K_Z.

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 2, "ms": 2, "hammer": 1, "crush": 1} *)
  Lemma fast_elements_tr_helper :
    forall (t : tree) (lst : list (key * V)),
      (fast_elements_tr t lst = elements t ++ lst)%list.
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    mirrorsolve.
  Qed.

  Hint Immediate fast_elements_tr_helper : tree_eqns.
  Hint Resolve fast_elements_tr_helper.

   (*** MS LEMMA {"original": False, "goals": 2, "ms": 2, "hammer": 2, "crush": 2} *)
  Lemma app_nil_r_K_V:
    forall (x: list (key * V)), (x ++ [] = x)%list.
  Proof.
    induction x;
    try hammer'.
    Restart.
    induction x;
    try crush'.
    Restart.
    induction x;
    mirrorsolve.
  Qed.

  Hint Immediate app_nil_r_K_V : tree_eqns.
  Hint Resolve app_nil_r_K_V.

  Hint Immediate fast_elements_equation_1 : tree_eqns.
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 0, "crush": 0} *)
  Lemma fast_elements_eq_elements : forall (t : tree),
      fast_elements t = elements t.
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
    mirrorsolve.
  Qed.

  Hint Immediate fast_elements_eq_elements : tree_eqns.
  Hint Resolve fast_elements_eq_elements.


(** [] *)

(** Since the two implementations compute the same function, all
    the results we proved about the correctness of [elements]
    also hold for [fast_elements].  For example: *)

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": False, "ho": False, "goals": 1, "ms": 1, "hammer": 0, "crush": 0} *)
  Corollary fast_elements_correct :
    forall (t: tree) (k : key) (v d : V),
      BST t ->
      In (k, v) (fast_elements t) ->
      bound_t k t = true /\ lookup_t d k t = v.
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
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

  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": True, "ho": False, "goals": 1, "ms": 1, "hammer": 1, "crush": 1} *)
  Lemma elements_empty :
      elements empty_tree = [].
  Proof.
    try hammer'.
    Restart.
    try crush'.
    Restart.
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

  Hint Immediate kvs_insert_equation_1 : tree_eqns.
  Hint Immediate kvs_insert_equation_2 : tree_eqns.

  (*** MS EFFORT {"type": "edit"} *)
  (*** MS LEMMA {"original": True, "sfo": False, "tsfo": False, "ho": False, "goals": 4, "ms": 4, "hammer": 2, "crush": 2} *)

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
    try hammer'.
    Restart.
    induction e1;
    induction e2.
    - try crush';
      admit.
    - try crush';
      admit.
    - try crush';
      admit.
    - try crush';
      admit.
    Restart.
    induction e1;
    induction e2;
    mirrorsolve.
  Qed.

  Hint Immediate kvs_insert_split' : tree_eqns.
  Hint Resolve kvs_insert_split'.
  (** **** Exercise: 3 stars, standard, optional (kvs_insert_elements) *)
  (*** MS LEMMA {"original": True, "sfo": True, "tsfo": False, "ho": False, "goals": 2, "ms": 2, "hammer": 2, "crush": 1} *)
  Lemma kvs_insert_elements : forall (t : tree),
      BST t ->
      forall (k : key) (v : V),
        elements (insert_t k v t) = kvs_insert k v (elements t).
  Proof.
    induction t;
    try hammer'.
    Restart.
    induction t;
    try crush'.
    Restart.
    induction t;
    mirrorsolve.
  Qed.

End SearchTree.
(*** MS EXTRA {"count": 17} *)
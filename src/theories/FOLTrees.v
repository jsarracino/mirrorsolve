From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.

Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.

Import ListNotations.
Import HListNotations.

Set Universe Polymorphism.

Require Import Coq.ZArith.BinInt.

Section Tree.
  (* type of values in the tree *)
  Variable (V: Type).

  Inductive tree :=
    | Emp
    | Node (l : tree) (k : Z) (v : V) (r : tree).

(** [bound k t] is whether [k] is bound in [t]. *)

  Fixpoint bound (x : Z) (t : tree) :=
    match t with
    | Emp => false
    | Node l y v r => 
      ite (x <? y)%Z (bound x l)
      (ite (x >? y)%Z (bound x r) true)
    end.

  Lemma bound_emp: 
    forall x, 
      bound x Emp = false.
  Proof. intros; exact eq_refl. Qed.

  Lemma bound_node: 
    forall x l y v r, 
      bound x (Node l y v r) = ( 
        ite (x <? y)%Z (bound x l)
        (ite (x >? y)%Z (bound x r) true)
      ).
  Proof. intros; exact eq_refl. Qed.

  (** [lookup d k t] is the value bound to [k] in [t], or is default
      value [d] if [k] is not bound in [t]. *)

  Fixpoint lookup (d : V) (x : Z) (t : tree) : V :=
    match t with
    | Emp => d
    | Node l y v r => 
      ite (x <? y)%Z (lookup d x l)
      (ite (x >? y)%Z (lookup d x r) v)
    end.

  Lemma lookup_emp: 
    forall d x, 
      lookup d x Emp = d.
  Proof. intros; exact eq_refl. Qed.

  Lemma lookup_node: 
    forall d x l y v r, 
      lookup d x (Node l y v r) = ( 
        ite (x <? y)%Z (lookup d x l)
        (ite (x >? y)%Z (lookup d x r) v)
      ).
  Proof. intros; exact eq_refl. Qed.

  (** [insert k v t] is the map containing all the bindings of [t] along
      with a binding of [k] to [v]. *)

  Fixpoint insert (x : Z) (v : V) (t : tree) : tree :=
    match t with
    | Emp => Node Emp x v Emp
    | Node l y v' r => 
      ite (x <? y)%Z (Node (insert x v l) y v' r)
      (ite (x >? y)%Z (Node l y v' (insert x v r))
        (Node l x v r)
      )
    end.

  Lemma insert_emp: 
    forall x v, 
      insert x v Emp = Node Emp x v Emp.
  Proof. intros; exact eq_refl. Qed.

  Lemma insert_node: 
    forall x v l y v' r, 
      insert x v (Node l y v' r) = ( 
        ite (x <? y)%Z (Node (insert x v l) y v' r)
        (ite (x >? y)%Z (Node l y v' (insert x v r))
          (Node l x v r)
        )
      ).
  Proof. intros; exact eq_refl. Qed.
End Tree.

Arguments Emp {_}.
Arguments Node {_} _ _ _ _.
Arguments bound {_} _ _.
Arguments lookup {_} _ _ _.
Arguments insert {_} _ _ _.

Section FOLTree.

  Variable (T: Type).

  Inductive sorts : Set := | TS | TreeS | BS | ZS.

  Scheme Equality for sorts.
  Set Universe Polymorphism.

  Inductive funs: arity sorts -> sorts -> Type :=
    | b_lit : forall (b: bool), funs [] BS
    | z_lt : funs [ZS; ZS] BS
    | z_gt : funs [ZS; ZS] BS
    | e_f : funs [] TreeS
    | t_f : funs [TreeS; ZS; TS; TreeS] TreeS
    | cond_b : funs [BS; BS; BS] BS
    | cond_t : funs [BS; TS; TS] TS
    | cond_tree : funs [BS; TreeS; TreeS] TreeS. 

  Inductive rels: arity sorts -> Type :=.

  Definition sig: signature :=
    {| sig_sorts := sorts;
      sig_funs := funs;
      sig_rels := rels |}.

  Definition fm ctx := FirstOrder.fm sig ctx.
  Definition tm ctx := FirstOrder.tm sig ctx.

  Definition mod_sorts (s: sig_sorts sig) : Type :=
    match s with
    | TreeS => tree T
    | TS => T
    | ZS => Z
    | BS => bool
    end.

  Obligation Tactic := idtac.
  Equations 
    mod_fns params ret (f: sig_funs sig params ret) (args: HList.t mod_sorts params) 
    : mod_sorts ret :=
    { 
      mod_fns _ _ (b_lit b) _ := b;
      mod_fns _ _ z_lt (l ::: r ::: _) := (l <? r)%Z;
      mod_fns _ _ z_gt (l ::: r ::: _) := (l >? r)%Z;
      mod_fns _ _ e_f _ := Emp;
      mod_fns _ _ t_f (l ::: k ::: v ::: r ::: _) := Node l k v r;
      mod_fns _ _ cond_b (t ::: l ::: r ::: _) := ite t l r;
      mod_fns _ _ cond_t (t ::: l ::: r ::: _) := ite t l r;
      mod_fns _ _ cond_tree (t ::: l ::: r ::: _) := ite t l r;
    }.

  Definition mod_rels params
    (args: sig_rels sig params)
    (env: HList.t mod_sorts params) : Prop :=
    match args with
    end.

  Program Definition fm_model : model sig := {|
    FirstOrder.mod_sorts := mod_sorts;
    FirstOrder.mod_fns := mod_fns;
    FirstOrder.mod_rels := mod_rels;
  |}.

End FOLTree.


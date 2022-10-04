Require Import Coq.Setoids.Setoid.

Lemma some_ty: 
  forall {T} {x x': T},
    Some x = Some x' <-> 
    x = x'.
Proof.
  intros.
  intuition (inversion H; eauto).
Qed.

Lemma some_prop: 
  forall p p': Prop,
    Some p = Some p' <-> 
    p = p'.
Proof.
  intros.
  eapply some_ty.
Qed.

Lemma iff_distribute:
  forall a b c d : Prop,
    (a <-> c) -> 
    (b <-> d) -> 
    ((a -> b) <-> (c -> d)).
Proof.
  intros.
  erewrite H.
  erewrite H0.
  eapply iff_refl.
Qed.

Ltac revert_hyp H := 
  refine ((_ : _ -> _) H); clear H.

Ltac revert_hyps := 
  repeat match goal with
  | H: _ |- _ => revert_hyp H
  end.

Ltac revert_all := 
  repeat match goal with
  | H: ?X |- _ => 
    match X with
    | Type => fail 1
    | _ => idtac
    end;
    (revert_hyp H || clear H || revert H)
  end.

Ltac pose_all Pfs := 
  match Pfs with 
  | (?Pfs', ?Pf) => pose proof Pf; pose_all Pfs'
  | _ => idtac
  end.

Section SetList.
  Require Import Coq.Lists.List.
  Variable (V: Type).
  Variable (eqb: V -> V -> bool).

  Fixpoint inb (x: V) (xs: list V) : bool := 
    match xs with 
    | nil => false
    | x' :: xs' => 
      if eqb x x' then true else inb x xs'
    end.

  Fixpoint uniq (xs: list V) : list V := 
    match xs with 
    | nil => nil
    | x :: xs' => 
      let r := uniq xs' in 
      if inb x r then r else x :: r
    end.

End SetList.

Section AssocList.

  Require Import Coq.Lists.List.

  Variable (K V: Type).
  Variable (eqb: K -> K -> bool).

  Fixpoint find (k: K) (xs: list (K * V)) : option V := 
    match xs with 
    | (k', v) :: xs' => 
      if eqb k k' then Some v else find k xs'
    | nil => None
    end.

  Definition find_all (ks: list K) (xs: list (K * V)) : list (K * V) := 
    List.fold_left (fun acc k => 
      match find k xs with 
      | Some v => (k, v) :: acc
      | None => acc
      end
    ) ks xs.

  Fixpoint remove (k: K) (xs: list (K * V)) : list (K * V) := 
    match xs with 
    | nil => nil
    | (k', v) :: xs' => 
      if eqb k k' then remove k xs' else (k', v) :: remove k xs'
    end.
  
  Definition remove_all (ks: list K) (xs: list (K * V)) : list (K * V) := 
    List.fold_left (fun xs k => remove k xs) ks xs.
  
  Definition assoc (k : K) (v : V) xs := (k, v) :: remove k xs.

  Definition left_union (ls: list (K * V)) (rs: list (K * V)) := 
    List.fold_left (fun xs '(k, v) => assoc k v xs) ls rs.

  Fixpoint update (k: K) (v: V) (xs: list (K * V)) : list (K * V) := 
    match xs with 
    | nil => nil
    | (k', v') :: xs' => 
      if eqb k k' then (k, v) :: xs' else (k', v') :: update k v xs'
    end.

  Definition update_all (orig: list (K * V)) (new: list (K * V)) := 
    List.fold_left (fun xs '(k, v) => update k v xs) new orig.


End AssocList.

Fixpoint join {K V V' eqb} (ls: list (K * V)) (rs: list (K * V')) : list (K * (V * V')) := 
  match ls with 
  | nil => nil
  | (k, v) :: ls' => 
    match find K V' eqb k rs with 
    | Some v' => 
      (k, (v, v')) :: join (eqb := eqb) ls' rs
    | None => join (eqb := eqb) ls' rs
    end
  end.


Fixpoint drop_last {A} (xs: list A) : list A := 
  match xs with 
  | nil => nil
  | x :: xs => 
    match xs with 
    | nil => nil
    | _ => x :: drop_last xs
    end
  end.

Definition flip {A B} (xs: list (A * B)) : list (B * A) := 
  map (fun '(x, y) => (y, x)) xs.

Fixpoint map_option {A B} (f: A -> option B) (xs: list A) : list B := 
  match xs with 
  | nil => nil
  | x :: xs' => 
    match f x with 
    | Some y => y :: map_option f xs'
    | None => map_option f xs'
    end
  end.

Fixpoint map_option_all {A B} (f: A -> option B) (xs: list A) : option (list B) := 
  match xs with 
  | nil => Some nil
  | x :: xs' => 
    match f x, map_option_all f xs' with 
    | Some y, Some ys' => Some (y :: ys')
    | _, _ => None
    end
  end.

Definition o2l {A} (x: option A) := 
  match x with 
  | Some x' => x' :: nil
  | None => nil
  end.

From MetaCoq.Template Require Import All.

(* Given a substitution key-value, if the LHS is a Coq variable, increment the DB indexing.
   This is useful when substituting under a product.
*)
Definition inc_subst_var {A} : term * A -> term * A := fun '(k, v) => 
  match k with 
  | tRel n => (tRel (S n), v)
  | _ => (k, v)
  end.

Require Import MirrorSolve.Reflection.Core.

(* Given an environment of key-value substitutions, replace all LHS with the corresponding RHS.
   Adjusts variable DB indices in the keys as it goes (i.e. to correctly substitute under binders)
*)
Fixpoint subst_terms (env: list (term * term)) (t: term) := 
  match find _ _ Core.eq_term t env with 
  | Some t' => t'
  | None => 
    match t with 
    | tApp f args => 
      tApp (subst_terms env f) (map (subst_terms env) args)
    | tProd x ty bod => 
      tProd x (subst_terms env ty) (subst_terms (map inc_subst_var env) bod)
    | _ => t 
    end
  end.
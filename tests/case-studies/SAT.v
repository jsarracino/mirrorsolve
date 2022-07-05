From Coq Require Export List.
From Coq Require Import Nat Recdef Lia.
Export ListNotations.

(* Verification of a simple SAT solver
 * -----------------------------------
 *)


(* Types defining the problem and solution
   ---------------------------------------

   The solver takes as input a query in CNF form, representing a conjunction of
   clauses, where each clause represents a conjunction of literals.

   Each literal represents a boolean variable (or its negation), and the goal of
   the solver is to produce a boolean assignation for each literal present in
   the input formula.
*)

(* A literal. [Pos n] corresponds to literal n, and [Neg n] to its negation.
*)
Inductive literal :=
  | Pos : nat -> literal
  | Neg : nat -> literal.

(* A clause represents a disjunction of literals *)
Definition clause := list literal.

(* A SAT problem in Conjunctive Normal Form:
   it corresponds to a conjunction of clauses *)
Definition cnf := list clause.

(* Example:

   The following cnf:
   [[Pos 1; Neg 2];
    [Neg 1; Pos 3; Pos 4]]

   corresponds to the boolean formula:
   (x1 \/ ~x2) /\
   (~x1 \/ x3 \/ x4)

   where x1, x2, x3 and x4 are boolean variables.
*)

(* The goal of the solver is to produce an assignment. We represent it as a list
   of literals, which correspond to the literals that are taken to be true.

   In other words, if the assignment list contains [Neg 3], then the boolean
   variable x3 should be assigned to false.

   Note: we generally only want to consider "valid" assignments, which do not
   include both a literal and its negation. We will come back to this later (see
   [valid_assignment]).
*)
Definition assignment := list literal.

(* In fact, the solver we implement will return a list of all possible
   solutions.

   (This would be terribly inefficient if we were to run the solver and compute
   the full list of solutions, but we can instead compute it using a
   call-by-name strategy (thus, the list of solutions becomes a lazy list), and
   only retrieve the first solution of the list.)
*)
Definition solutions := list assignment.


(* Helper functions and lemmas
   ---------------------------

   Mainly define the (computable) equality function on literals,
   literal negation, and associated lemmas.
*)

(* Some auxiliary functions on literals. *)
Definition lit_eqb (l1 l2: literal): bool :=
  match l1, l2 with
  | Pos u, Pos v
  | Neg u, Neg v => u =? v
  | _, _ => false
  end.

Lemma lit_eqb_eq l1 l2: lit_eqb l1 l2 = true <-> l1 = l2.
Proof.
  destruct l1, l2; cbn; try now (split; congruence).
  all: rewrite PeanoNat.Nat.eqb_eq; split; congruence.
Qed.

Lemma lit_eqb_neq l1 l2 : lit_eqb l1 l2 = false <-> l1 <> l2.
Proof.
  destruct l1, l2; cbn; try now (split; congruence).
  all: rewrite PeanoNat.Nat.eqb_neq; split; congruence.
Qed.

Definition lit_neg (l: literal): literal :=
  match l with
  | Pos n => Neg n
  | Neg n => Pos n
  end.

Lemma lit_neg_idemp (l: literal) : lit_neg (lit_neg l) = l.
Proof. destruct l; auto. Qed.

(* The size of a CNF, defined as the the number of its literals.
   Used to prove termination of the solver. *)
Fixpoint cnf_size (c: cnf): nat :=
  match c with
  | [] => 0
  | cl :: rest => length cl + cnf_size rest
  end.

Ltac case_if :=
  match goal with
    |- context [if ?b then _ else _] =>
    destruct b eqn:?
  end.

Lemma existsb_lit_notin l c : existsb (lit_eqb l) c = false <-> ~ In l c.
Proof.
  split.
  { intros ? ?. enough (existsb (lit_eqb l) c = true) by congruence.
    apply existsb_exists. eexists; split; eauto. apply lit_eqb_eq; auto. }
  { intros HH. destruct (existsb (lit_eqb l) c) eqn:Heq; auto. exfalso.
    apply existsb_exists in Heq as [? [? ->%lit_eqb_eq]]. apply HH. auto. }
Qed.



(* The solver definition
   ------------------------

   This is the implementation of the SAT solver itself.

   Its main function is [resolve]. It relies on the [propagate] auxiliary
   function, which implements literal propagation.

   The high-level intuition is that [propagate l c] takes a literal [l] and a
   cnf [c], and, assuming that [l] is to be assigned to true, simplifies [c]
   into a new cnf which does not rely on [l] or [lit_neg l] anymore.


   The [_variant] lemmas can be ignored, they are only used in the (included)
   proof of termination for defining [resolve].
*)

Definition remove_lit (l: literal) (cl: clause) :=
  List.filter (fun l' => negb (lit_eqb l l')) cl.

Fixpoint propagate (l: literal) (c: cnf) : cnf :=
  match c with
  | [] => []
  | cl :: rest =>
    if List.existsb (lit_eqb l) cl
    then propagate l rest
    else (remove_lit (lit_neg l) cl) :: (propagate l rest)
  end.

Lemma remove_lit_variant (l: literal) (cl: clause):
  length (remove_lit l cl) <= length cl.
Proof.
  induction cl as [| ? ? IHcl]; cbn; try case_if; cbn; auto.
  unfold remove_lit in IHcl. lia.
Qed.

Lemma propagate_variant (l: literal) (c: cnf):
  cnf_size (propagate l c) <= cnf_size c.
Proof.
  induction c as [| cl c IHc]; cbn; auto.
  case_if; cbn; try lia. pose proof (remove_lit_variant (lit_neg l) cl).
  lia.
Qed.

Function resolve (c: cnf) {measure cnf_size c}: solutions :=
  match c with
  | [] => [[]]
  | cl :: rest =>
    match cl with
    | [] => []
    | l :: cl' =>
      let c1 := propagate l rest in
      let c2 := propagate (lit_neg l) (cl' :: rest) in
      let solutions1 := List.map (List.cons l) (resolve c1) in
      let solutions2 := List.map (List.cons (lit_neg l)) (resolve c2) in
      solutions1 ++ solutions2
    end
  end.
Proof.
  (* Proof of termination *)
  all: intros c cl rest l cl'; intros -> ->; cbn.
  { destruct (existsb (lit_eqb (lit_neg l))); cbn.
    - pose proof (propagate_variant (lit_neg l) rest). lia.
    - pose proof (remove_lit_variant (lit_neg (lit_neg l)) cl').
      pose proof (propagate_variant (lit_neg l) rest). lia. }
  { pose proof (propagate_variant l rest). lia. }
Defined.

(* NB: Function generates an induction principle for [resolve], and a lemma to
   unfold its body. You will need to use them. *)
Check resolve_ind.
Check resolve_equation.


(* Interpretation of clauses and cnf
   ------------------------------------

   Given an assignment, we can "evaluate" a clause/a cnf as a boolean.
   This is done by the [interp] functions below.
 *)

Fixpoint interp_clause (cl: clause) (a: assignment): bool :=
  match cl with
  | [] => false
  | l :: cl' => List.existsb (lit_eqb l) a || interp_clause cl' a
  end.

Fixpoint interp (c: cnf) (a: assignment): bool :=
  match c with
  | [] => true
  | cl :: rest => interp_clause cl a && interp rest a
  end.



(* To prove correctness of [resolve] in the unsat case we will need to define
what a *valid* assignment is, i.e. one that does not contain both a literal and
its negation. *)
Definition valid_assignment (a: assignment) :=
  forall (l: literal),
    List.In l a ->
    ~ List.In (lit_neg l) a.

    From Coq Require Import List Nat Recdef Lia.
    Import ListNotations.
    
    
    (* 1) Correctness of solutions returned by [resolve]
    -------------------------------------------------
    
       A first correctness lemma: assignments produced by [resolve] are correct wrt
       [interp].
    *)
    
    (* The core of the proof relies on a similar correctness lemma for [propagate]. *)
    Lemma propagate_correct (a: assignment) (l: literal) (c: cnf) :
      interp (propagate l c) a = true ->
      interp c (l :: a) = true.
    Admitted.
    
    Lemma resolve_correct (c: cnf) (a: assignment):
      List.In a (resolve c) ->
      interp c a = true.
    Admitted.
    
    
    
    (* 2) Correctness of [resolve] in the unsat case
       ---------------------------------------------
    
       If [resolve] returns no solutions (the empty list), then the input CNF should
       be unsatisfiable.
    
       To formally state this property, we first need to define what a *valid*
       assignment is, i.e. one that does not contain both a literal and its negation.
    *)
    
    (* You will need to formulate a lemma for [propagate], in a similar vein as
       [propagate_correct].
    
       However, there's an extra subtlety here. Think: does the following hold
       if (lit_neg) is in a?
    
         interp (propagate l c) a = false ->
         interp c (l :: a) = false
    *)
    
    Lemma resolve_unsat_correct (c: cnf):
      resolve c = [] ->
      forall a, valid_assignment a -> interp c a = false.
    Admitted.
    
    
    (* ==== This part is OPTIONAL and it is NOT graded. === *)
    (* ==== We keep this for the sake of completeness of the specification === *)
    (* ==== but exclude it from grading to keep the task complexity at bay. === *)
    
    (* 3) Validity of assignments produced by [resolve]
       ------------------------------------------------
    
       To complete the proof of the solver, we finally need to prove that it only
       produces valid assignments. Otherwise, a solver could simply return an
       assignment containing every literal and its negation, which would be
       considered as a valid solution according to [interp].
    
       The key idea is to prove that, for any literal that appears in an assignment
       returned by [resolve c], then either the literal or its negation were present
       in [c].
    *)
    
    (* useful helper lemmas *)
    Lemma valid_assignment_nil : valid_assignment [].
    Proof. intros ? ?. cbn in *. auto. Qed.
    
    Lemma valid_assignment_cons a l:
      valid_assignment a ->
      ~ List.In (lit_neg l) a ->
      valid_assignment (l :: a).
    Proof.
      intros Hv Ha l'. cbn. intros [->|Hl'].
      { intros HH. apply Ha. destruct HH; auto. exfalso.
        destruct l'; cbn in *; congruence. }
      { intros [?|HH].
        { subst l. rewrite lit_neg_idemp in Ha. auto. }
        { eapply (Hv l' Hl'); auto. } }
    Qed.
    
    Lemma resolve_valid (c: cnf) (a: assignment):
      List.In a (resolve c) ->
      valid_assignment a.
    Admitted.
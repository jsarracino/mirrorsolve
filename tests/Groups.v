(* Copyright (c) 2008-2012, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

Require Import MirrorSolve.SMT.
Require Import MirrorSolve.BV.

 Require Import Eqdep List Omega.

 Set Implicit Arguments.
 
 
 (** A version of [injection] that does some standard simplifications afterward: clear the hypothesis in question, bring the new facts above the double line, and attempt substitution for known variables. *)
 Ltac inject H := injection H; clear H; intros; try subst.
 
 (** Try calling tactic function [f] on all hypotheses, keeping the first application that doesn't fail. *)
 Ltac appHyps f :=
   match goal with
     | [ H : _ |- _ ] => f H
   end.
 
 (** Succeed iff [x] is in the list [ls], represented with left-associated nested tuples. *)
 Ltac inList x ls :=
   match ls with
     | x => idtac
     | (_, x) => idtac
     | (?LS, _) => inList x LS
   end.
 
 (** Try calling tactic function [f] on every element of tupled list [ls], keeping the first call not to fail. *)
 Ltac app f ls :=
   match ls with
     | (?LS, ?X) => f X || app f LS || fail 1
     | _ => f ls
   end.
 
 (** Run [f] on every element of [ls], not just the first that doesn't fail. *)
 Ltac all f ls :=
   match ls with
     | (?LS, ?X) => f X; all f LS
     | (_, _) => fail 1
     | _ => f ls
   end.
 
 (** Workhorse tactic to simplify hypotheses for a variety of proofs.
    * Argument [invOne] is a tuple-list of predicates for which we always do inversion automatically. *)
 Ltac simplHyp invOne :=
   (** Helper function to do inversion on certain hypotheses, where [H] is the hypothesis and [F] its head symbol *)
   let invert H F :=
     (** We only proceed for those predicates in [invOne]. *)
     inList F invOne;
     (** This case covers an inversion that succeeds immediately, meaning no constructors of [F] applied. *)
       (inversion H; fail)
     (** Otherwise, we only proceed if inversion eliminates all but one constructor case. *)
       || (inversion H; [idtac]; clear H; try subst) in
 
   match goal with
     (** Eliminate all existential hypotheses. *)
     | [ H : ex _ |- _ ] => destruct H
 
     (** Find opportunities to take advantage of injectivity of data constructors, for several different arities. *)
     | [ H : ?F ?X = ?F ?Y |- ?G ] =>
       (** This first branch of the [||] fails the whole attempt iff the arguments of the constructor applications are already easy to prove equal. *)
       (assert (X = Y); [ assumption | fail 1 ])
       (** If we pass that filter, then we use injection on [H] and do some simplification as in [inject].
          * The odd-looking check of the goal form is to avoid cases where [injection] gives a more complex result because of dependent typing, which we aren't equipped to handle here. *)
       || (injection H;
         match goal with
           | [ |- X = Y -> G ] =>
             try clear H; intros; try subst
         end)
     | [ H : ?F ?X ?U = ?F ?Y ?V |- ?G ] =>
       (assert (X = Y); [ assumption
         | assert (U = V); [ assumption | fail 1 ] ])
       || (injection H;
         match goal with
           | [ |- U = V -> X = Y -> G ] =>
             try clear H; intros; try subst
         end)
 
     (** Consider some different arities of a predicate [F] in a hypothesis that we might want to invert. *)
     | [ H : ?F _ |- _ ] => invert H F
     | [ H : ?F _ _ |- _ ] => invert H F
     | [ H : ?F _ _ _ |- _ ] => invert H F
     | [ H : ?F _ _ _ _ |- _ ] => invert H F
     | [ H : ?F _ _ _ _ _ |- _ ] => invert H F
 
     (** Use an (axiom-dependent!) inversion principle for dependent pairs, from the standard library. *)
     | [ H : existT _ ?T _ = existT _ ?T _ |- _ ] => generalize (inj_pair2 _ _ _ _ _ H); clear H
 
     (** If we're not ready to use that principle yet, try the standard inversion, which often enables the previous rule. *)
     | [ H : existT _ _ _ = existT _ _ _ |- _ ] => inversion H; clear H
 
     (** Similar logic to the cases for constructor injectivity above, but specialized to [Some], since the above cases won't deal with polymorphic constructors. *)
     | [ H : Some _ = Some _ |- _ ] => injection H; clear H
   end.
 
 (** Find some hypothesis to rewrite with, ensuring that [auto] proves all of the extra subgoals added by [rewrite]. *)
 Ltac rewriteHyp :=
   match goal with
     | [ H : _ |- _ ] => rewrite H by solve [ auto ]
   end.
 
 (** Combine [autorewrite] with automatic hypothesis rewrites. *)
 Ltac rewriterP := repeat (rewriteHyp; autorewrite with core in *).
 Ltac rewriter := autorewrite with core in *; rewriterP.
 
 (** This one is just so darned useful, let's add it as a hint here. *)
 Hint Rewrite app_ass.
 
 (** Devious marker predicate to use for encoding state within proof goals *)
 Definition done (T : Type) (x : T) := True.
 
 (** Try a new instantiation of a universally quantified fact, proved by [e].
    * [trace] is an accumulator recording which instantiations we choose. *)
 Ltac inster e trace :=
   (** Does [e] have any quantifiers left? *)
   match type of e with
     | forall x : _, _ =>
       (** Yes, so let's pick the first context variable of the right type. *)
       match goal with
         | [ H : _ |- _ ] =>
           inster (e H) (trace, H)
         | _ => fail 2
       end
     | _ =>
       (** No more quantifiers, so now we check if the trace we computed was already used. *)
       match trace with
         | (_, _) =>
           (** We only reach this case if the trace is nonempty, ensuring that [inster] fails if no progress can be made. *)
           match goal with
             | [ H : done (trace, _) |- _ ] =>
               (** Uh oh, found a record of this trace in the context!  Abort to backtrack to try another trace. *)
               fail 1
             | _ =>
               (** What is the type of the proof [e] now? *)
               let T := type of e in
                 match type of T with
                   | Prop =>
                     (** [e] should be thought of as a proof, so let's add it to the context, and also add a new marker hypothesis recording our choice of trace. *)
                     generalize e; intro;
                       assert (done (trace, tt)) by constructor
                   | _ =>
                     (** [e] is something beside a proof.  Better make sure no element of our current trace was generated by a previous call to [inster], or we might get stuck in an infinite loop!  (We store previous [inster] terms in second positions of tuples used as arguments to [done] in hypotheses.  Proofs instantiated by [inster] merely use [tt] in such positions.) *)
                     all ltac:(fun X =>
                       match goal with
                         | [ H : done (_, X) |- _ ] => fail 1
                         | _ => idtac
                       end) trace;
                     (** Pick a new name for our new instantiation. *)
                     let i := fresh "i" in (pose (i := e);
                       assert (done (trace, i)) by constructor)
                 end
           end
       end
   end.
 
 (** After a round of application with the above, we will have a lot of junk [done] markers to clean up; hence this tactic. *)
 Ltac un_done :=
   repeat match goal with
            | [ H : done _ |- _ ] => clear H
          end.
 
 Require Import JMeq.
 
 (** A more parameterized version of the famous [crush].  Extra arguments are:
    * - A tuple-list of lemmas we try [inster]-ing 
    * - A tuple-list of predicates we try inversion for *)
 Ltac crush' lemmas invOne :=
   (** A useful combination of standard automation *)
   let sintuition := simpl in *; intuition; try subst;
     repeat (simplHyp invOne; intuition; try subst); try congruence in
 
   (** A fancier version of [rewriter] from above, which uses [crush'] to discharge side conditions *)
   let rewriter := autorewrite with core in *;
     repeat (match goal with
               | [ H : ?P |- _ ] =>
                 match P with
                   | context[JMeq] => fail 1 (** JMeq is too fancy to deal with here. *)
                   | _ => rewrite H by crush' lemmas invOne
                 end
             end; autorewrite with core in *) in
 
   (** Now the main sequence of heuristics: *)
     (sintuition; rewriter;
       match lemmas with
         | false => idtac (** No lemmas?  Nothing to do here *)
         | _ =>
           (** Try a loop of instantiating lemmas... *)
           repeat ((app ltac:(fun L => inster L L) lemmas
           (** ...or instantiating hypotheses... *)
             || appHyps ltac:(fun L => inster L L));
           (** ...and then simplifying hypotheses. *)
           repeat (simplHyp invOne; intuition)); un_done
       end;
       sintuition; rewriter; sintuition;
       (** End with a last attempt to prove an arithmetic fact with [omega], or prove any sort of fact in a context that is contradictory by reasoning that [omega] can do. *)
       try omega; try (elimtype False; omega)).
 
 (** [crush] instantiates [crush'] with the simplest possible parameters. *)
 Ltac crush := time "crush" (crush' false fail).
 
 (** * Wrap Program's [dependent destruction] in a slightly more pleasant form *)
 
 Require Import Program.Equality.
 
 (** Run [dependent destruction] on [E] and look for opportunities to simplify the result.
    The weird introduction of [x] helps get around limitations of [dependent destruction], in terms of which sorts of arguments it will accept (e.g., variables bound to hypotheses within Ltac [match]es). *)
 Ltac dep_destruct E :=
   let x := fresh "x" in
     remember E as x; simpl in x; dependent destruction x;
       try match goal with
             | [ H : _ = E |- _ ] => try rewrite <- H in *; clear H
           end.
 
 (** Nuke all hypotheses that we can get away with, without invalidating the goal statement. *)
 Ltac clear_all :=
   repeat match goal with
            | [ H : _ |- _ ] => clear H
          end.
 
 (** Instantiate a quantifier in a hypothesis [H] with value [v], or, if [v] doesn't have the right type, with a new unification variable.
    * Also prove the lefthand sides of any implications that this exposes, simplifying [H] to leave out those implications. *)
 Ltac guess v H :=
   repeat match type of H with
            | forall x : ?T, _ =>
              match type of T with
                | Prop =>
                  (let H' := fresh "H'" in
                    assert (H' : T); [
                      solve [ eauto 6 ]
                      | specialize (H H'); clear H' ])
                  || fail 1
                | _ =>
                  specialize (H v)
                  || let x := fresh "x" in
                    evar (x : T);
                    let x' := eval unfold x in x in
                      clear x; specialize (H x')
              end
          end.
 
 (** Version of [guess] that leaves the original [H] intact *)
 Ltac guessKeep v H :=
   let H' := fresh "H'" in
     generalize H; intro H'; guess v H'.
 

(* pulled from: https://people.cs.umass.edu/~arjun/courses/cs691pl-spring2014/assignments/groups.html *)

(* The set of the group. *)
Parameter G : Set.

(* The binary operator. *)
Parameter f : G -> G -> G.

(* The group identity. *)
Parameter e : G.

(* The inverse operator. *)
Parameter i : G -> G.

(* For readability, we use infix <+> to stand for the binary operator. *)
Infix "<+>" := f (at level 50, left associativity).

(* The operator [f] is associative. *)
Axiom assoc : forall a b c, a <+> b <+> c = a <+> (b <+> c).

(* [e] is the right-identity for all elements [a] *)
Axiom id_r : forall a, a <+> e = a.

(* [i a] is the right-inverse of [a]. *)
Axiom inv_r : forall a, a <+> i a = e.

Lemma mult_both : 
  forall a b c d1 d2, 
    a <+> c = d1
    -> b <+> c = d2
    -> a = b
    -> d1 = d2.
  crush.
Qed.

Hint Extern 100 (_ = _) =>
match goal with
  | [ _ : True |- _ ] => fail 1
  | _ => assert True by constructor; eapply mult_both 
end.

Hint Resolve inv_r.

Lemma inv_r' : 
  forall x y, 
    x = y <+> i y -> 
    x = e.
Proof.
  crush.
Qed.

Lemma unique_id : forall a, a <+> a = a -> a = e.
  intros.
  assert (a <+> i a = a <+> i a) by trivial.
  erewrite <- H in H0 at 1.
  erewrite assoc in H0.
  erewrite inv_r in H0.
  erewrite id_r in H0.
  auto.
Qed.


(* [i a] is the left-inverse of [a]. *)
Lemma inv_l : forall a, i a <+> a = e.
Proof.
  intros.
  eapply unique_id.
  erewrite <- assoc.
  erewrite assoc with (a := i a).
  erewrite inv_r.
  erewrite id_r.
  trivial.
Qed.
(* [e] is the left-identity. *)
Lemma id_l : forall a, e <+> a = a.
Proof.
  intros.
  erewrite <- inv_r with (a := a).
  erewrite assoc.
  erewrite inv_l.
  erewrite id_r.
  trivial.
Qed.

(* [x] can be cancelled on the right. *)
Lemma cancel_r : forall a b x, a <+> x = b <+> x -> a = b.
Proof.
  intros.
  assert (a <+> x <+> i x = a <+> x <+> i x) by trivial.
  erewrite H in H0 at 1.
  repeat erewrite assoc in H0.
  repeat erewrite inv_r in H0.
  repeat erewrite id_r in H0.
  auto.
Qed.
  

(* [x] can be cancelled on the left. *)
Lemma cancel_l: forall a b x, x <+> a = x <+> b -> a = b.
Proof.
  intros.
  assert (i x <+> x <+> a = i x <+> x <+> a) by trivial.
  erewrite assoc in H0.
  erewrite H in H0 at 1.
  repeat erewrite <- assoc in H0.
  erewrite inv_l in H0.
  repeat erewrite id_l in H0.
  auto.
Qed.

(* The left identity is unique. *)
Lemma e_uniq_l : forall a p, p <+> a = a -> p = e.
Proof.
  intros.
  eapply cancel_r.
  erewrite <- id_l in H.
  eauto.
Qed.
(* The left inverse is unique. *)
Lemma inv_uniq_l : forall a b, a <+> b = e -> a = i b.
Proof.
  intros.
  eapply cancel_r.
  erewrite <- inv_l in H.
  eauto.
Qed.

(* The left identity is unique. *)
Lemma e_uniq_r : forall a p, a <+> p = a -> p = e.
Proof.
  intros.
  eapply cancel_l.
  erewrite <- id_r in H.
  eauto.
Qed.

(* The right inverse is unique. *)
Lemma inv_uniq_r : forall a b, a <+> b = e -> b = i a.
Proof.
  intros.
  eapply cancel_l.
  erewrite <- inv_r in H.
  eauto.
Qed.

(* The inverse operator distributes over the group operator. *)
Lemma inv_distr : forall a b, i (a <+> b) = i b <+> i a.
Proof.
  intros.
  eapply eq_sym.
  eapply inv_uniq_r.
  erewrite <- assoc.
  assert (a <+> b <+> i b <+> i a = a <+> (b <+> i b) <+> i a) by (now erewrite <- assoc).
  erewrite H.
  erewrite inv_r.
  erewrite id_r.
  eapply inv_r.
Qed.
(* The inverse of an inverse produces the original element. *)
Lemma double_inv : forall a, i (i a) = a.
Proof.
  intros.
  eapply eq_sym.
  eapply inv_uniq_r.
  eapply inv_l.
Qed.
(* The identity is its own inverse. *)
Lemma id_inv : i e = e.
Proof.
  intros.
  eapply eq_sym.
  eapply inv_uniq_r.
  eapply id_r.
Qed.




(* encoding in FOL *)

Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.Groups.

Require Import MirrorSolve.UF.

Require Import Coq.Strings.String.

Import ListNotations.

Set Universe Polymorphism.

Definition group_model := Groups.fm_model G e.

(* Parameter f : G -> G -> G.
Parameter i : G -> G. *)

Definition symbs : list (string * list (sig_sorts MirrorSolve.Groups.sig) * sig_sorts MirrorSolve.Groups.sig) := ([
  ("op", [G'; G'], G');
  ("inv", [G'], G')
]%string).
Definition group_uf_model := UF.fm_model Groups.sig group_model symbs.

Require Import MirrorSolve.HLists.
Require Import Coq.Lists.List.

Import HListNotations.
Import ListNotations.

Require Import Coq.Strings.String.

Lemma in_op : 
  In ("op"%string, [G'; G'], G') symbs.
Proof.
  simpl.
  left; trivial.
Defined.

Lemma in_inv : 
  In ("inv"%string, [G'], G') symbs.
Proof.
  simpl.
  right.
  left; trivial.
Defined.

Notation sig := (MirrorSolve.Groups.sig).
Notation sig' := (UF.sig sig symbs).
Notation OP := (UFun sig symbs in_op).
Notation INV := (UFun sig symbs in_inv).

Notation v_c := (VHere _ _ _). 
Notation v_b := (VThere _ _ _ _ v_c).
Notation v_a := (VThere _ _ _ _ v_b).  

(* group axioms *)
(* Axiom assoc : forall a b c, a <+> b <+> c = a <+> (b <+> c). *)
Definition assoc_fol {c} : fm sig symbs c :=
  FForall _ (FForall _ (FForall _ 
    (FEq 
      (TFun sig' OP 
        ( 
          (TFun sig' OP ((TVar v_a) ::: (TVar v_b) ::: hnil)) ::: 
          (TVar v_c) ::: hnil
        ))
      (TFun sig' OP 
        ( 
          (TVar v_a) ::: 
          (TFun sig' OP ((TVar v_b) ::: (TVar v_c) ::: hnil)) ::: hnil
        ))
    )
  )).

(* Axiom id_r : forall a, a <+> e = a. *)
Definition id_r_fol {c} : fm sig symbs c :=
  FForall _ 
    (FEq 
      (TFun sig' OP 
        ( 
          (TVar v_c) ::: (TFun sig' (CFun sig _ ELit) hnil) ::: hnil
        ))
      (TVar v_c)
    ).

  
  (* Axiom inv_r : forall a, a <+> i a = e. *)
Definition inv_r_fol {c} : fm sig symbs c :=
  FForall _ 
    (FEq 
      (TFun sig' OP 
        ( 
          (TVar v_c) ::: 
          (TFun sig' INV (TVar v_c ::: hnil)) ::: hnil
        ))
      (TFun sig' (CFun sig _ ELit) hnil)
    ). 

(* interpret a formula in the context of the group axioms *)

Definition group_fm_fol {c} (f: fm sig symbs c) : fm sig symbs c := 
  FImpl assoc_fol (
    FImpl id_r_fol (
      FImpl inv_r_fol f
    )
  ).

Definition interp_group_fm {c v} (f: fm sig symbs c) : Prop := 
  interp_fm (m := group_uf_model) v (group_fm_fol f).

(* Lemma unique_id : forall a, a <+> a = a -> a = e. *)
Definition unique_id_fol_fm : fm sig symbs (SLNil _) :=
  FForall _ (
    FImpl 
      (FEq 
        (TFun sig' OP (TVar v_c ::: TVar v_c ::: hnil)) 
        (TVar v_c))
      (FEq (TVar v_c) (TFun sig' (CFun sig _ ELit) hnil))
  ).

Notation PLUS := (interp_symbs _ _ _ "op" _ _ _).
Notation NEG := (interp_symbs _ _ _ "inv" _ _ _).

Local Declare ML Module "mirrorsolve".

(* RegisterCustomSort BS "BS".

RegisterSMTUF "power" ZS ZS BS. *)

RegisterCustomSort Groups.G' "G".

RegisterSMTUF "e" G'.

RegisterSMTFun ELit "e" 0.

(* Goal interp_fm (m := group_uf_model) (VEmp _ _)
  (FEq 
    (TFun sig' (CFun sig _ ELit) hnil)
    (TFun sig' (CFun sig _ ELit) hnil)
  ).
Proof.
  match goal with 
  | |- ?G => check_interp_pos G
  end.
Admitted. *)

RegisterSMTUF "op" G' G' G'.
Goal interp_fm (m := group_uf_model) (VEmp _ _)
  (FEq 
    (TFun sig' (CFun sig _ ELit) hnil)
    (TFun sig' (CFun sig _ ELit) hnil)
  ).
Proof.
  match goal with 
  | |- ?G => check_interp_pos G
  end.
Admitted.
RegisterSMTUF "inv" G' G'.

Lemma unique_id_fol : interp_group_fm (v := VEmp _ _) unique_id_fol_fm.
Proof.
  unfold interp_group_fm, unique_id_fol_fm, group_fm_fol.
  set (a := assoc_fol).
  set (b := id_r_fol).
  set (c := inv_r_fol).
  set (d := v_c).
  vm_compute in a, b, c, d.
  subst a.
  subst b.
  subst c.
  subst d.
  match goal with 
  | |- ?G => check_interp_pos G
  end.
Admitted.

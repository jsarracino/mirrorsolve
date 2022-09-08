Require Import MirrorSolve.FirstOrder.

Require Import MirrorSolve.BV.
Require Import MirrorSolve.SMT.
Require Import MirrorSolve.UF.

Require Import MirrorSolve.FOList.

Require Import MirrorSolve.HLists.
Require Import Coq.Lists.List.

Import HListNotations.
Import ListNotations.

Require Import Coq.Strings.String.

Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.

Require Import Coq.ZArith.BinInt.

Require Import Ascii.
Require Import List.

Inductive regexp : Type :=
| Zero   : regexp
| One    : regexp
| Lit    : ascii -> regexp
| Plus   : regexp -> regexp -> regexp
| Times  : regexp -> regexp -> regexp
| Star   : regexp -> regexp.

Inductive matches : regexp -> list ascii -> Prop :=
| m_One : matches One nil
| m_Lit : forall (c:ascii), matches (Lit c) [c]
| m_l_Plus : forall R1 R2 s, matches R1 s -> matches (Plus R1 R2) s
| m_r_Plus : forall R1 R2 s, matches R2 s -> matches (Plus R1 R2) s
| m_Times : forall R1 R2 s1 s2, matches R1 s1 -> matches R2 s2 -> matches (Times R1 R2) (s1 ++ s2)
| m_0_Star : forall R, matches (Star R) []
| m_n_Star : forall R s1 s2, matches R s1 -> matches (Star R) s2 -> matches (Star R) (s1 ++ s2).

Equations emp (R:regexp) : regexp := {
    emp Zero := Zero ;
    emp One := One ; 
    emp (Lit _) := Zero; 
    emp (Plus R1 R2) := Plus (emp R1) (emp R2);
    emp (Times R1 R2) := Times (emp R1) (emp R2);
    emp (Star R) := One
  }.

Equations is_emp (R:regexp) : bool := {
    is_emp Zero := false ;
    is_emp One := true ;
    is_emp (Lit _) := false ;
    is_emp (Plus R1 R2) := (is_emp R1) || (is_emp R2) ;
    is_emp (Times R1 R2) := (is_emp R1) && (is_emp R2) ;
    is_emp (Star R) := true
  }.

Equations deriv (c:ascii) (R:regexp) : regexp := {
    deriv _ Zero := Zero ;
    deriv _ One := Zero ;
    deriv c (Lit c') := if Ascii.eqb c c' then One else Zero ;
    deriv c (Plus R1 R2) := Plus (deriv c R1) (deriv c R2) ;
    deriv c (Times R1 R2) := Plus (Times (deriv c R1) R2) (Times (emp R1) (deriv c R2)) ;
    deriv c (Star R) := Times (deriv c R) (Star R)
  }.

Equations derivs (s:list ascii) (R:regexp) : bool := {
    derivs nil R := is_emp R ;
    derivs (c::s') R := derivs s' (deriv c R)
  }.                           

Definition matches_dec (R:regexp) (s:list ascii) : bool :=
  derivs s R.


Lemma emp_is_emp : forall R, is_emp R = true -> matches (emp R) nil.
Proof.
  induction R ; simpl ; intros ; autorewrite with is_emp in * ; autorewrite with emp in * ;
    try discriminate.
  constructor.
  destruct (is_emp R1) ; destruct (is_emp R2) ; simpl in *.
  constructor ; auto.
  constructor ; auto.
  apply m_r_Plus ; auto.
  discriminate.
  destruct (is_emp R1) ; destruct (is_emp R2) ; simpl in * ; try discriminate.
  replace [] with (@nil ascii ++ nil).
  constructor ; auto. auto.
  constructor.
Qed.


(*** Starting Encoding stuff ***)

Inductive fol_sorts :=
  sort_ascii | sort_list_ascii | sort_regexp | sort_bool.

Definition interp_sorts (x:fol_sorts) : Type :=
  match x with
  | sort_ascii => ascii
  | sort_list_ascii => list ascii
  | sort_regexp => regexp
  | sort_bool => bool
  end.

Inductive fol_regexp_fns : list fol_sorts -> fol_sorts -> Type :=
| nil_f : fol_regexp_fns [] sort_list_ascii
| cons_f : fol_regexp_fns [sort_ascii ; sort_list_ascii] sort_list_ascii
| app_f : fol_regexp_fns [sort_list_ascii ; sort_list_ascii] sort_list_ascii
| eqb_f : fol_regexp_fns [sort_ascii ; sort_ascii] sort_bool
| one_f : fol_regexp_fns [] sort_regexp
| zero_f : fol_regexp_fns [] sort_regexp
| lit_f : fol_regexp_fns [sort_ascii] sort_regexp
| plus_f : fol_regexp_fns [sort_regexp ; sort_regexp ] sort_regexp
| times_f : fol_regexp_fns [sort_regexp ; sort_regexp ] sort_regexp
| star_f : fol_regexp_fns [sort_regexp] sort_regexp
| emp_f : fol_regexp_fns [sort_regexp] sort_regexp
| is_emp_f : fol_regexp_fns [sort_regexp] sort_bool
| andb_f : fol_regexp_fns [sort_bool ; sort_bool] sort_bool
| orb_f : fol_regexp_fns [sort_bool ; sort_bool] sort_bool
| true_f : fol_regexp_fns [] sort_bool
| false_f : fol_regexp_fns [] sort_bool.

Inductive fol_regexp_rels : list fol_sorts -> Type :=
| matches_r : fol_regexp_rels [sort_regexp ; sort_list_ascii].

Definition regexp_sig : signature :=
  {| sig_sorts := fol_sorts ;
    sig_funs := fol_regexp_fns ;
    sig_rels := fol_regexp_rels
  |}.

Equations interp_fun args ret (f:fol_regexp_fns args ret) (hargs: HList.t interp_sorts args) : interp_sorts ret := {
    interp_fun _ _  nil_f _ := nil ;
    interp_fun _ _  cons_f (x:::l:::hnil) := x :: l ;
    interp_fun _ _  app_f (x:::y:::hnil) := x ++ y ;
    interp_fun _ _  eqb_f (x:::y:::hnil) := Ascii.eqb x y ;
    interp_fun _ _  one_f _ := One ;
    interp_fun _ _  zero_f _ := Zero ;
    interp_fun _ _  lit_f (c:::hnil) := Lit c ;
    interp_fun _ _  plus_f (r1:::r2:::hnil) := Plus r1 r2 ;
    interp_fun _ _  times_f (r1:::r2:::hnil) := Times r1 r2 ;
    interp_fun _ _  star_f (r:::hnil) := Star r ;
    interp_fun _ _  emp_f (r:::hnil) := emp r ;
    interp_fun _ _  is_emp_f (r:::hnil) := is_emp r ;
    interp_fun _ _  andb_f (b1:::b2:::hnil) := andb b1 b2 ; 
    interp_fun _ _  orb_f (b1:::b2:::hnil) := orb b1 b2 ; 
    interp_fun _ _  true_f _ := true ; 
    interp_fun _ _  false_f _ := false
    }.

Equations interp_rel args (r: fol_regexp_rels args) (hargs : HList.t interp_sorts args) : Prop := {
    interp_rel _ matches_r (r:::s:::hnil) := matches r s
  }.

Program Definition fm_model : model regexp_sig :=
  {|
    FirstOrder.mod_sorts := interp_sorts ;
    FirstOrder.mod_fns := interp_fun ;
    FirstOrder.mod_rels := interp_rel ;
  |}.


MetaCoq Quote Definition t_nil := @nil.
MetaCoq Quote Definition t_cons := @cons.
MetaCoq Quote Definition t_app := @app.
MetaCoq Quote Definition t_eqb := Ascii.eqb.
MetaCoq Quote Definition t_one := One.
MetaCoq Quote Definition t_zero := Zero.
MetaCoq Quote Definition t_lit := Lit.
MetaCoq Quote Definition t_plus := Plus.
MetaCoq Quote Definition t_times := Times.
MetaCoq Quote Definition t_star := Star.
MetaCoq Quote Definition t_emp := emp.
MetaCoq Quote Definition t_is_emp := is_emp.
MetaCoq Quote Definition t_andb := andb.
MetaCoq Quote Definition t_orb := orb.
MetaCoq Quote Definition t_true := true.
MetaCoq Quote Definition t_false := false.

MetaCoq Quote Definition t_ascii := ascii.
MetaCoq Quote Definition t_list_ascii := (list ascii).
MetaCoq Quote Definition t_regexp := regexp.
MetaCoq Quote Definition t_bool := bool.

MetaCoq Quote Definition t_matches := matches.

Require Import MirrorSolve.Reflection.Tactics.

Notation tac_fun_regexp f := (tac_fun regexp_sig f).
Notation tac_rel_regexp f := (tac_rel regexp_sig f).


Definition match_tacs : list ((term -> bool) * tac_syn regexp_sig fm_model) := [
( fun t => eq_ctor t t_nil, tac_fun_regexp nil_f) ; 
( fun t => eq_ctor t t_cons,tac_fun_regexp cons_f) ; 
( fun t => eq_ctor t t_app, tac_fun_regexp app_f) ; 
( fun t => eq_term t t_eqb, tac_fun_regexp eqb_f) ; 
( fun t => eq_term t t_one, tac_fun_regexp one_f) ;
( fun t => eq_term t t_zero, tac_fun_regexp zero_f) ; 
( fun t => eq_ctor t t_lit, tac_fun_regexp lit_f);
( fun t => eq_ctor t t_plus, tac_fun_regexp plus_f);
( fun t => eq_ctor t t_times, tac_fun_regexp times_f);
( fun t => eq_ctor t t_star, tac_fun_regexp star_f);
( fun t => eq_term t t_emp, tac_fun_regexp emp_f);
( fun t => eq_term t t_is_emp, tac_fun_regexp is_emp_f);
( fun t => eq_term t t_andb, tac_fun_regexp andb_f);
( fun t => eq_term t t_orb, tac_fun_regexp orb_f);
( fun t => eq_term t t_true, tac_fun_regexp true_f);
( fun t => eq_term t t_false, tac_fun_regexp false_f);
( fun t => eq_term t t_matches, tac_rel_regexp matches_r)
  ].
                                      
Definition match_inds : list ((term->bool) * fol_sorts) := [
    (eq_term t_ascii, sort_ascii) ;
    (eq_term t_list_ascii, sort_list_ascii) ;
    (eq_term t_regexp, sort_regexp) ; 
    (eq_term t_bool, sort_bool) 
  ].

Declare ML Module "mirrorsolve".

RegisterCustomSort sort_ascii "Ascii".

RegisterSMTInd sort_list_ascii (SICases [
      ("cons"%string, [SISort (SCustom "Ascii"); SIRec]) 
    ; ("nil"%string, []) 
  ]) "Ascii_list".

RegisterSMTInd sort_regexp (SICases [
  ("one"%string, []) ;
  ("zero"%string, []) ;
  ("lit"%string, [SISort (SCustom "Ascii")]);
  ("plus"%string, [SIRec ; SIRec]) ;
  ("times"%string, [SIRec ; SIRec]) ;
  ("star"%string, [SIRec])
  ]) "Regexp".

RegisterSMTSort sort_bool SBool.

RegisterSMTUF "app" sort_list_ascii sort_list_ascii sort_list_ascii.
RegisterSMTUF "emp" sort_regexp sort_regexp.
RegisterSMTUF "is_emp" sort_regexp sort_bool.
RegisterSMTUF "matches" sort_regexp sort_list_ascii sort_bool.



RegisterSMTFun nil_f "nil" 0.
RegisterSMTFun cons_f "cons" 2.
RegisterSMTFun app_f "app" 2.
RegisterSMTFun eqb_f "=" 2.
RegisterSMTFun one_f "one" 0.
RegisterSMTFun zero_f "zero" 0.
RegisterSMTFun lit_f "lit" 1.
RegisterSMTFun plus_f "plus" 2.
RegisterSMTFun times_f "times" 2.
RegisterSMTFun star_f "star" 1.
RegisterSMTFun emp_f "emp" 1.
RegisterSMTFun is_emp_f "is_emp" 1.
RegisterSMTFun andb_f "and" 2.
RegisterSMTFun orb_f "or" 2.
RegisterSMTFun true_f "true" 0.
RegisterSMTFun false_f "false" 0.
RegisterSMTFun matches_r "matches" 2.

Transparent denote_tm.
Require Import MirrorSolve.Axioms.

Ltac check_goal_unsat := 
  match goal with 
  | |- ?G => check_unsat_neg G; eapply UnsoundAxioms.interp_true
  end.

Create HintDb regexp_eqns.

Hint Resolve emp_equation_1 : regexp_eqns.
Hint Resolve emp_equation_2 : regexp_eqns.
Hint Resolve emp_equation_3 : regexp_eqns.
Hint Resolve emp_equation_4 : regexp_eqns.
Hint Resolve emp_equation_5 : regexp_eqns.
Hint Resolve emp_equation_6 : regexp_eqns.

Hint Resolve is_emp_equation_1 : regexp_eqns.
Hint Resolve is_emp_equation_2 : regexp_eqns.
Hint Resolve is_emp_equation_3 : regexp_eqns.
Hint Resolve is_emp_equation_4 : regexp_eqns.
Hint Resolve is_emp_equation_5 : regexp_eqns.
Hint Resolve is_emp_equation_6 : regexp_eqns.

Lemma matches_one : forall s, matches One s <-> s = nil.
Proof.
  split ; intros ; subst ; auto. inversion H ; auto. constructor.
Qed.
Hint Resolve matches_one : regexp_eqns.

Lemma matches_zero : forall s, matches Zero s <-> False.
Proof.
  split ; intros ; auto. inversion H.
Qed.
Hint Resolve matches_zero : regexp_eqns.

Lemma matches_lit : forall c s, matches (Lit c) s <-> s = c::nil.
Proof.
  intros ; split ; intro. inversion H ; subst ; auto.
  subst ; constructor.
Qed.
Hint Resolve matches_lit : regexp_eqns.

Lemma matches_plus : forall r1 r2 s, matches (Plus r1 r2) s <-> matches r1 s \/ matches r2 s.
Proof.
  intros ; split ; intros.
  inversion H ; auto. destruct H. constructor ; auto. apply m_r_Plus ; auto.
Qed.
Hint Resolve matches_plus : regexp_eqns.

(*
Lemma matches_times : forall r1 r2 s, matches (Times r1 r2) s <-> exists s1, exists s2, s = s1 ++ s2 /\ matches r1 s1 /\ matches r2 s2. 
Proof.
  intros ; split ; intros.
  inversion H ; subst.
  eauto.
  destruct H as [s1 [s2 [H1 [H2 H3]]]]. subst ; constructor ; auto.
Qed.
*)

Lemma matches_times1 : forall r1 r2 s1 s2 s3, 
  matches r1 s1 -> 
  matches r2 s2 -> 
  s3 = s1 ++ s2 ->
  matches (Times r1 r2) s3.
Proof.
  intros;
  subst.
  constructor ; auto.
Qed.
Hint Resolve matches_times1 : regexp_eqns.

(*
Lemma matches_star1 : forall r r' s, matches r s -> r = Star r' -> matches One s \/ matches (Times r' r) s.
Proof.
  induction r ; intros ; try discriminate. injection H0 ; intros ; subst.
  inversion H ; subst. left ; constructor.
  admit.

    
Lemma matches_star : forall r s, matches (Star r) s <-> matches One s \/ matches (Times r (Star r)) s.
Proof.
 *)


Ltac prep_proof := 
    hints_foreach (fun x => pose proof x) "regexp_eqns";
    Utils.revert_all;
    unfold "<->" in *.

Scheme Equality for fol_sorts.

Ltac quote_reflect_list := quote_reflect regexp_sig fm_model fol_sorts_eq_dec match_tacs match_inds.
Ltac quote_extract_list := quote_extract regexp_sig fm_model fol_sorts_eq_dec match_tacs match_inds.


Ltac mirrorsolve :=
    prep_proof;
    quote_reflect_list;
    check_goal_unsat.

SetSMTSolver "z3".

Lemma app_nil_l: 
  forall (x: list ascii), [] ++ x = x.
Proof.
  intros; simpl; trivial.
Qed.

Lemma app_cons_l: 
  forall c (l r: list ascii),  (c :: l) ++ r = c :: (l ++ r).
Proof.
  intros; simpl; trivial.
Qed.

Hint Immediate app_nil_l : regexp_eqns.
Hint Immediate app_cons_l : regexp_eqns.

Lemma app_nil_r: 
  forall (x: list ascii), x ++ [] = x.
Proof.
  induction x; mirrorsolve.
Qed.

Hint Immediate app_nil_r : regexp_eqns.

SetSMTSolver "cvc5".

Lemma emp_is_emp' : forall R, is_emp R = true -> matches (emp R) nil.
Proof.
  (* assert (@nil ascii = @nil ascii ++ []) by mirrorsolve. *)
  induction R ; 
  try mirrorsolve.
Qed.
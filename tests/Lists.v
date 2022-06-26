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

Section ListFuncs.
  Variable (A: Type).

  Fixpoint app (l: list A) (r: list A) := 
    match l with 
    | nil => r
    | x :: l' => x :: app l' r
    end.

  Lemma app_nil: 
    forall xs, 
      app nil xs = xs.
  Proof.
    intros; exact eq_refl.
  Qed.

  Lemma app_cons: 
    forall x xs ys, 
      app (x :: xs) ys = x :: (app xs ys).
  Proof.
    intros; exact eq_refl.
  Qed.

  Fixpoint my_rev (xs: list A) :=
    match xs with 
    | nil => nil
    | x :: xs' => app (my_rev xs') [x]
    end. 

  Lemma my_rev_nil: 
    my_rev nil = nil.
  Proof.
    intros; exact eq_refl.
  Qed.

  Lemma my_rev_cons: 
    forall x xs, 
      my_rev (x :: xs) = app (my_rev xs) [x].
  Proof.
    intros; exact eq_refl.
  Qed.

  Fixpoint tail_app (acc: list A) (l_rev: list A) : list A := 
    match l_rev with 
    | nil => acc
    | (l :: l_rev') => tail_app (l :: acc) l_rev'
    end. 

  Lemma tail_app_nil: 
    forall acc, 
      tail_app acc nil = acc.
  Proof.
    intros; exact eq_refl.
  Qed.

  Lemma tail_app_cons: 
    forall acc x xs, 
      tail_app acc (x :: xs) = tail_app (x :: acc) xs.
  Proof.
    intros; exact eq_refl.
  Qed.
  
  Definition my_app l r := tail_app r (my_rev l).

  From Hammer Require Import Hammer.

  Set Hammer ATPLimit 5.
  Set Hammer ReconstrLimit 10.

  (* we will model this using three UF functions, for rev, app, and tail_app *)


  Set Universe Polymorphism.

  Notation sig := FOList.sig.

  Definition list_model := FOList.fm_model A.

  (* First, set up uninterpreted function symbols for app, rev, and tail_rev *)
  Definition symbs : list (string * list (sig_sorts sig) * sig_sorts sig) := ([
    ("app", [LS; LS], LS); 
    ("rev", [LS], LS); 
    ("tail_app", [LS; LS], LS) 
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
  Definition interp_syms (sym: string) (a: list (sig_sorts sig)) (r: sig_sorts sig) (H: In (sym, a, r) symbs) (args: HList.t (FirstOrder.mod_sorts sig list_model) a) : FirstOrder.mod_sorts sig list_model r.
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
    - exact (app X X1).
    - exact (my_rev X).
    - exact (tail_app X X1).
  Defined.

  Definition list_uf_model := UF.fm_model sig list_model symbs interp_syms.


  Notation sig' := (UF.sig sig symbs).

  Require Import MirrorSolve.Reflection.Core.
  Require Import MirrorSolve.Reflection.FM.
  Require Import MirrorSolve.Reflection.Tactics.

  MetaCoq Quote Definition t_app := @app.
  MetaCoq Quote Definition t_rev := @my_rev.
  MetaCoq Quote Definition t_tail_app := @tail_app.

  MetaCoq Quote Definition t_cons := @cons.
  MetaCoq Quote Definition t_nil := @nil.

  (* Some match tactics for the meta-interpreter. 
    The meta-interpreter converts these definitions into a reflection procedure between pure Coq goals and FOL terms in the UF + Lists combined theory. 
  *)

  Definition is_cons t :=
    match t with 
    | tApp f _ => eq_term t_cons f
    | _ => false
    end.

  Definition is_nil t :=
    match t with 
    | tApp f _ => eq_term t_nil f
    | _ => false
    end.

  Definition is_app t := 
    match t with 
    | tApp f _ => eq_term t_app f
    | _ => false
    end.

  Definition is_rev t := 
    match t with 
    | tApp f _ => eq_term t_rev f
    | _ => false
    end.

  Definition is_tail_app t := 
    match t with 
    | tApp f _ => eq_term t_tail_app f
    | _ => false
    end.

  Definition match_tacs : list ((term -> bool) * tac_syn sig' list_uf_model) := [
      ( is_nil, tacFun _ _ (Mk_fun_sym sig' _ _ (CFun _ symbs nil_f)))
    ; ( is_cons, tacFun _ _ (Mk_fun_sym sig' _ _ (CFun _ symbs cons_f)))
    ; ( is_app, tacFun _ _ (Mk_fun_sym sig' _ _ (UFun (s := "app") _ symbs ltac:(solve_uf_membership))))
    ; ( is_rev, tacFun _ _ (Mk_fun_sym sig' _ _ (UFun (s := "rev") _ symbs ltac:(solve_uf_membership))))
    ; ( is_tail_app, tacFun _ _ (Mk_fun_sym sig' _ _ (UFun (s := "tail_app") _ symbs ltac:(solve_uf_membership))))
  ].

  MetaCoq Quote Definition t_sort := (A).
  MetaCoq Quote Definition list_sort := (list A).

  (* This is an analogous match but for reflecting Coq types into FOL sorts. *)
  Definition match_inds : list ((term -> bool) * FOList.sorts) := [
      (eq_term t_sort, TS)
    ; (eq_term list_sort, LS)
  ].


  Local Declare ML Module "mirrorsolve".
  RegisterCustomSort TS "A".

  RegisterSMTInd LS (SICases [
    ("cons"%string, [SISort (SCustom "A"); SIRec]); 
    ("nil"%string, [])
    ]) "A_list".

  RegisterSMTUF "app" LS LS LS.
  RegisterSMTUF "rev" LS LS.
  RegisterSMTUF "tail_app" LS LS LS.

  Transparent denote_tm.

  RegisterSMTFun FOList.nil_f "nil" 0.
  RegisterSMTFun FOList.cons_f "cons" 2.

  Require Import MirrorSolve.Axioms.

  Ltac check_goal_sat := 
    match goal with 
    | |- ?G => check_interp_pos G; eapply UnsoundAxioms.interp_true
    end.
  Ltac check_goal_unsat := 
    match goal with 
    | |- ?G => check_unsat_neg G; eapply UnsoundAxioms.interp_true
    end.

  MetaCoq Quote Definition app_app_nil := (
    (forall (x : A) (xs ys : list A), app (x :: xs) ys = x :: app xs ys) ->
(forall xs : list A, app [] xs = xs) ->
forall (a : A) (r : list A), app (app [] [a]) r = app [] (a :: r)
  ).

  MetaCoq Quote Definition app_app_cons := (
    (forall (x : A) (xs ys : list A), app (x :: xs) ys = x :: app xs ys) ->
    (forall xs : list A, app [] xs = xs) ->
    forall (a a0 : A) (l : list A),
    (forall r : list A, app (app l [a]) r = app l (a :: r)) ->
    forall r : list A, app (app (a0 :: l) [a]) r = app (a0 :: l) (a :: r)
  ).

  (* Hammer works for this one *)
  Lemma app_app_one : 
    forall (a: A) (l r : list A), 
      app (app l [a]) r = app l (a :: r).
  Proof.
    (* induction l; try hammer. *)

    pose proof app_cons.
    pose proof app_nil. 
    Utils.revert_all.
    induction l; Utils.revert_all.
    
    - 
      reflect_goal (UF.sig sig symbs) list_uf_model sorts_eq_dec match_tacs match_inds app_app_nil. 
      check_goal_unsat.
    -
      reflect_goal (UF.sig sig symbs) list_uf_model sorts_eq_dec match_tacs match_inds app_app_cons. 
      check_goal_unsat.
  Qed.

  MetaCoq Quote Definition app_nil_r_nil := (
    (forall xs : list A, app [] xs = xs) ->
(forall (x : A) (xs ys : list A), app (x :: xs) ys = x :: app xs ys) ->
app [] [] = []
  ).

  MetaCoq Quote Definition app_nil_r_cons := (
    (forall xs : list A, app [] xs = xs) ->
    (forall (x : A) (xs ys : list A), app (x :: xs) ys = x :: app xs ys) ->
    forall (a : A) (l : list A), app l [] = l -> app (a :: l) [] = a :: l
  ).

  (* hammer works for this one *)
  Lemma app_nil_r : 
    forall l, app l [] = l.
  Proof.
    pose proof app_nil.
    pose proof app_cons.
    induction l; Utils.revert_all.
    - 
      reflect_goal (UF.sig sig symbs) list_uf_model sorts_eq_dec match_tacs match_inds app_nil_r_nil. 
      check_goal_unsat.
    - 
      reflect_goal (UF.sig sig symbs) list_uf_model sorts_eq_dec match_tacs match_inds app_nil_r_cons. 
      check_goal_unsat.
  Qed.

  MetaCoq Quote Definition app_assoc_nil := (
    (forall xs : list A, app [] xs = xs) ->
(forall (x : A) (xs ys : list A), app (x :: xs) ys = x :: app xs ys) ->
(forall l : list A, app l [] = l) ->
forall ys zs : list A, app (app [] ys) zs = app [] (app ys zs)
  ).

  MetaCoq Quote Definition app_assoc_cons := (
    (forall xs : list A, app [] xs = xs) ->
    (forall (x : A) (xs ys : list A), app (x :: xs) ys = x :: app xs ys) ->
    (forall l : list A, app l [] = l) ->
    forall (a : A) (xs : list A),
    (forall ys zs : list A, app (app xs ys) zs = app xs (app ys zs)) ->
    forall ys zs : list A, app (app (a :: xs) ys) zs = app (a :: xs) (app ys zs)
  ).

  (* hammer works for this one *)
  Lemma app_assoc : 
    forall xs ys zs, app (app xs ys) zs = app xs (app ys zs).
  Proof.
    pose proof app_nil.
    pose proof app_cons.
    pose proof app_nil_r.
    induction xs; Utils.revert_all.
    - 
      reflect_goal (UF.sig sig symbs) list_uf_model sorts_eq_dec match_tacs match_inds app_assoc_nil. 
      check_goal_unsat.
    - 
      reflect_goal (UF.sig sig symbs) list_uf_model sorts_eq_dec match_tacs match_inds app_assoc_cons. 
      check_goal_unsat.
  Qed.

  MetaCoq Quote Definition rev_app_nil := (
    (forall l : list A, app l [] = l) ->
    my_rev [] = [] ->
    (forall (x : A) (xs : list A), my_rev (x :: xs) = app (my_rev xs) [x]) ->
    (forall xs : list A, app [] xs = xs) ->
    (forall (x : A) (xs ys : list A), app (x :: xs) ys = x :: app xs ys) ->
    forall r : list A, my_rev (app [] r) = app (my_rev r) (my_rev [])
  ).

  MetaCoq Quote Definition rev_app_cons := (
    (forall xs ys zs : list A, app (app xs ys) zs = app xs (app ys zs)) ->
    my_rev [] = [] ->
    (forall (x : A) (xs : list A), my_rev (x :: xs) = app (my_rev xs) [x]) ->
    (forall xs : list A, app [] xs = xs) ->
    (forall (x : A) (xs ys : list A), app (x :: xs) ys = x :: app xs ys) ->
    forall (a : A) (l : list A),
    (forall r : list A, my_rev (app l r) = app (my_rev r) (my_rev l)) ->
    forall r : list A, my_rev (app (a :: l) r) = app (my_rev r) (my_rev (a :: l))
  ).
  

  (* hammer does not work for the inductive case *)
  Lemma rev_app : 
    forall l r, 
      my_rev (app l r) = app (my_rev r) (my_rev l).
  Proof.
    (* induction l; try hammer. *)
    pose proof my_rev_nil.
    pose proof my_rev_cons.
    pose proof app_nil.
    pose proof app_cons.
    Utils.revert_all.
    induction l; Utils.revert_all.
    - 
      pose proof app_nil_r.
      Utils.revert_all.
      reflect_goal (UF.sig sig symbs) list_uf_model sorts_eq_dec match_tacs match_inds rev_app_nil. 
      check_goal_unsat.
    - 
      pose proof app_assoc.
      Utils.revert_all.
      reflect_goal (UF.sig sig symbs) list_uf_model sorts_eq_dec match_tacs match_inds rev_app_cons. 
      check_goal_unsat.
  Qed.

  MetaCoq Quote Definition rev_rev_nil := (
    my_rev [] = [] ->
(forall (x : A) (xs : list A), my_rev (x :: xs) = app (my_rev xs) [x]) ->
(forall xs : list A, app [] xs = xs) ->
(forall (x : A) (xs ys : list A), app (x :: xs) ys = x :: app xs ys) ->
my_rev (my_rev []) = []
  ).

  MetaCoq Quote Definition rev_rev_cons := (
    (forall l r : list A, my_rev (app l r) = app (my_rev r) (my_rev l)) ->
    (forall xs ys zs : list A, app (app xs ys) zs = app xs (app ys zs)) ->
    (forall l : list A, app l [] = l) ->
    my_rev [] = [] ->
    (forall (x : A) (xs : list A), my_rev (x :: xs) = app (my_rev xs) [x]) ->
    (forall xs : list A, app [] xs = xs) ->
    (forall (x : A) (xs ys : list A), app (x :: xs) ys = x :: app xs ys) ->
    forall (a : A) (l : list A),
    my_rev (my_rev l) = l -> my_rev (my_rev (a :: l)) = a :: l
  ).


  (* hammer works for this one *)
  Lemma rev_rev : 
    forall (l : list A), 
      my_rev (my_rev l) = l.
  Proof.
    (* induction l; try hammer. *)
    pose proof my_rev_nil.
    pose proof my_rev_cons.
    pose proof app_nil.
    pose proof app_cons.
    induction l; Utils.revert_all.
    - 
      reflect_goal (UF.sig sig symbs) list_uf_model sorts_eq_dec match_tacs match_inds rev_rev_nil.
      check_goal_unsat.
    - 
      pose proof rev_app.
      pose proof app_assoc.
      pose proof app_nil_r.
      Utils.revert_all.
      reflect_goal (UF.sig sig symbs) list_uf_model sorts_eq_dec match_tacs match_inds rev_rev_cons.
      
      check_goal_unsat.
  Qed.

  MetaCoq Quote Definition tail_app_rev_nil := (
    (forall acc : list A, tail_app acc [] = acc) ->
    (forall (acc : list A) (x : A) (xs : list A),
     tail_app acc (x :: xs) = tail_app (x :: acc) xs) ->
    my_rev [] = [] ->
    (forall (x : A) (xs : list A), my_rev (x :: xs) = app (my_rev xs) [x]) ->
    (forall xs : list A, app [] xs = xs) ->
    (forall (x : A) (xs ys : list A), app (x :: xs) ys = x :: app xs ys) ->
    forall acc : list A, tail_app acc [] = app (my_rev []) acc
  ).

  MetaCoq Quote Definition tail_app_rev_cons := (
    (forall l r : list A, my_rev (app l r) = app (my_rev r) (my_rev l)) ->
    (forall xs ys zs : list A, app (app xs ys) zs = app xs (app ys zs)) ->
    (forall l : list A, app l [] = l) ->
    (forall l : list A, my_rev (my_rev l) = l) ->
    (forall acc : list A, tail_app acc [] = acc) ->
    (forall (acc : list A) (x : A) (xs : list A),
     tail_app acc (x :: xs) = tail_app (x :: acc) xs) ->
    my_rev [] = [] ->
    (forall (x : A) (xs : list A), my_rev (x :: xs) = app (my_rev xs) [x]) ->
    (forall xs : list A, app [] xs = xs) ->
    (forall (x : A) (xs ys : list A), app (x :: xs) ys = x :: app xs ys) ->
    forall (a : A) (l : list A),
    (forall acc : list A, tail_app acc l = app (my_rev l) acc) ->
    forall acc : list A, tail_app acc (a :: l) = app (my_rev (a :: l)) acc
  ).
 
  (* hammer does not work for the inductive case *)
  Lemma tail_app_rev : 
    forall (l: list A) acc, 
      tail_app acc l = app (my_rev l) acc.
  Proof.
    (* induction l; try hammer. *)
    pose proof tail_app_nil.
    pose proof tail_app_cons.
    pose proof my_rev_nil.
    pose proof my_rev_cons.
    pose proof app_nil.
    pose proof app_cons.
    induction l; Utils.revert_all.
    - 
      reflect_goal (UF.sig sig symbs) list_uf_model sorts_eq_dec match_tacs match_inds tail_app_rev_nil.
      check_goal_unsat.
    - 
      pose proof rev_app.
      pose proof app_assoc.
      pose proof app_nil_r.
      pose proof rev_rev.
      Utils.revert_all.
      reflect_goal (UF.sig sig symbs) list_uf_model sorts_eq_dec match_tacs match_inds tail_app_rev_cons.
      check_goal_unsat.
  Qed.

  MetaCoq Quote Definition my_app_sound_term := (
    (forall acc : list A, tail_app acc [] = acc) ->
    (forall (acc : list A) (x : A) (xs : list A),
     tail_app acc (x :: xs) = tail_app (x :: acc) xs) ->
    my_rev [] = [] ->
    (forall (x : A) (xs : list A), my_rev (x :: xs) = app (my_rev xs) [x]) ->
    (forall xs : list A, app [] xs = xs) ->
    (forall (x : A) (xs ys : list A), app (x :: xs) ys = x :: app xs ys) ->
    (forall l : list A, my_rev (my_rev l) = l) ->
    (forall l acc : list A, tail_app acc l = app (my_rev l) acc) ->
    forall l r : list A, tail_app r (my_rev l) = app l r
  ).

  (* hammer works for this one *)
  Theorem my_app_sound:
    forall l r,
      my_app l r = app l r.
  Proof.
    (* unfold my_app; try hammer. *)
    pose proof tail_app_nil.
    pose proof tail_app_cons.
    pose proof my_rev_nil.
    pose proof my_rev_cons.
    pose proof app_nil.
    pose proof app_cons.
    pose proof rev_rev.
    pose proof tail_app_rev.
    Utils.revert_all.
    unfold my_app.
    reflect_goal (UF.sig sig symbs) list_uf_model sorts_eq_dec match_tacs match_inds my_app_sound_term.
    check_goal_unsat.
  Qed.

End ListFuncs.
  
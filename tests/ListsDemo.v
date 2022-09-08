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

Section ListFuncs.
  Variable (A: Type).

  Inductive list := nil | cons : A -> list -> list.

  Infix "::" := cons.

  Equations app (l: list) (r: list) : list := {
    app nil r := r;
    app (x :: l') r := x :: app l' r;
  }.

  Equations rev (xs: list) : list := {
    rev nil := nil;
    rev (x :: l') := app (rev l') (x :: nil);
  }.

  Equations len (xs: list) : Z := {
    len nil := 0;
    len (_ :: xs) := len xs + 1;
  }.

  Inductive fol_sorts := sort_A | sort_lA | sort_Z | sort_bool.
  Definition interp_sorts (x: fol_sorts) : Type := 
    match x with 
    | sort_A => A
    | sort_lA => list
    | sort_Z => Z
    | sort_bool => bool
    end.

  (* Next we define function symbols for everything mentioned in the functions:
    nil, cons, my_app, my_rev, tail_rev, my_len, Z plus, Z constants

    We also define a relation symbol for my_In.

    Our functions and relations have dependent types; functions are indexed by the argument types and return type,
    and relations are indexed by the argument types. The argument types are encoded as a list of fol_sorts symbols.
  
  *)
  
  Inductive fol_list_funs : List.list fol_sorts -> fol_sorts -> Type := 
    | nil_f : fol_list_funs [] sort_lA
    | cons_f : fol_list_funs [sort_A; sort_lA] sort_lA
    | my_app_f : fol_list_funs [sort_lA; sort_lA] sort_lA
    | my_rev_f : fol_list_funs [sort_lA] sort_lA
    | my_len_f : fol_list_funs [sort_lA] sort_Z
    | plus_f : fol_list_funs [sort_Z; sort_Z] sort_Z
    | z_const_f : forall (z: Z), fol_list_funs [] sort_Z.

  Inductive fol_list_rels : List.list fol_sorts -> Type := .

  (* We package these up into a first-order logic *signature* for lists: the type symbols + function + relation symbols. 
  
  *)

  Definition list_sig: signature := {| 
    sig_sorts := fol_sorts;
    sig_funs := fol_list_funs;
    sig_rels := fol_list_rels 
  |}.

  (* Next we give a semantics to the function and relation symbols, in terms of the original functions and relation.
    We use equations because the semantics has a dependent type (the sort symbols are interpreted for arguments and results).
    The interpreted arguments are provided in a HList input.
  *)

  Equations interp_fun args ret (f: fol_list_funs args ret) (hargs : HList.t interp_sorts args) : interp_sorts ret := {
    interp_fun _ _ nil_f _ := nil;
    interp_fun _ _ cons_f (x ::: l ::: hnil):= x :: l;
    interp_fun _ _ my_app_f (l ::: r ::: hnil):= app l r;
    interp_fun _ _ my_rev_f (x ::: hnil) := rev x;
    interp_fun _ _ my_len_f (x ::: hnil) := len x;
    interp_fun _ _ plus_f (l ::: r ::: hnil) := (l + r)%Z;
    interp_fun _ _ (z_const_f z) hnil := z;
  }.
  
  Equations interp_rel args (r: fol_list_rels args) (hargs : HList.t interp_sorts args) : Prop := {
  }.

  Program Definition fm_model : model list_sig := {|
    FirstOrder.mod_sorts := interp_sorts;
    FirstOrder.mod_fns := interp_fun;
    FirstOrder.mod_rels := interp_rel;
  |}.

  MetaCoq Quote Definition t_cons := @ListFuncs.cons.
  MetaCoq Quote Definition t_nil := @ListFuncs.nil.
  MetaCoq Quote Definition t_my_app := @ListFuncs.app.
  MetaCoq Quote Definition t_my_rev := @ListFuncs.rev.
  MetaCoq Quote Definition t_my_len := @ListFuncs.len.
  MetaCoq Quote Definition t_plus := @Z.add.

  (* z constants are handled by a mirrorsolve primitive *)

  (* Next we need boolean tests for checking whether a metacoq AST term is a particular quoted value *)
  Definition is_t_cons t :=  eq_ctor t t_cons.
  Definition is_t_nil t :=  eq_term t t_nil.
  Definition is_t_my_app t :=  eq_ctor t t_my_app.
  Definition is_t_my_rev t :=  eq_ctor t t_my_rev.
  Definition is_t_my_len t :=  eq_ctor t t_my_len.
  Definition is_t_plus t :=  eq_ctor t t_plus.

  (* We also need to quote the types: Z, A, and list A *)
  MetaCoq Quote Definition t_Z := (Z).
  MetaCoq Quote Definition t_lA := (@ListFuncs.list).
  MetaCoq Quote Definition t_A := (A).
  MetaCoq Quote Definition t_bool := (bool).
  

  (* Next we have some machinery for reflecting between normal Coq goals and goals in FOL,
    and we start with some helper notation for calling mirrorsolve conversion functions. 
     Plain function and relation symbols are easy so mirrorsolve can auto-generate reflection code.
     More complicated symbols are harder; 
      for example the function symbol for Z literals is tricky because it quantifies over all Z values.
     Mirrorsolve has a primitive for converting Z constants which we use here.
   *)

  Require Import MirrorSolve.Reflection.Tactics.

  Notation tac_fun_list f := (tac_fun list_sig f).
  Notation tac_rel_list f := (tac_rel list_sig f).

  (* This line is really tricky to understand, I wouldn't puzzle through the details unless you're really curious! *)
  Notation tac_z_list := (tacLit list_sig fm_model z_lit (fun x => (sort_Z; x)) (fun x _ => (sort_Z; TFun list_sig (z_const_f x) hnil)) ltac:(solve_lit_wf)).

  (* List of reflection matches; the first element is a test function and the second is a conversion tactic to apply.
   *)
  Definition match_tacs : List.list ((term -> bool) * tac_syn list_sig fm_model) := [
      ( is_t_cons, tac_fun_list cons_f)
    ; ( is_t_nil, tac_fun_list nil_f)
    ; ( is_t_my_app, tac_fun_list my_app_f)
    ; ( is_t_my_rev, tac_fun_list my_rev_f)
    ; ( is_t_my_len, tac_fun_list my_len_f)
    ; ( is_t_plus, tac_fun_list plus_f)
    ; ( is_z_term, tac_z_list )
  ].

  (* Analogous reflection matches for sorts *)
  Definition match_inds : List.list ((term -> bool) * fol_sorts) := [
      (eq_term t_lA, sort_lA)
    ; (eq_term t_A, sort_A)
    ; (eq_term t_Z, sort_Z)
    ; (eq_term t_bool, sort_bool)
  ].

  (* Next we configure the backend SMT plugin. *)

  Declare ML Module "mirrorsolve".

  (* The section variable A is an uninterpreted sort in SMT. *)
  RegisterCustomSort sort_A "A".

  (*  The inductive sort list A maps to an inductive smt sort,
      specified as a sum (coq list) of products (also a coq list),
      with cons and nil constructors.
  *)
  RegisterSMTInd sort_lA (SICases [
      ("cons"%string, [SISort (SCustom "A"); SIRec]) (* This declares an smt constructor named cons with an "A" argument and a recursive argument (i.e. the inner list) *)
    ; ("nil"%string, []) (* This declares an smt constructor named nil with no arguments *)
  ]) "A_list".

  (* Map the Z sort to SMT Int, and the bool sort to SMT bool *)
  RegisterSMTSort sort_Z SInt.
  RegisterSMTSort sort_bool SBool.

  (* The inductive declaration puts "cons" and "nil" in scope as SMT function symbols, 
    but the rest of our functions/relations still need to be declared. 
    We do this with the RegisterSMTUF vernacular. 
    The syntax for this vernacular is:

    RegisterSMTUF "<function name>" sorts.

    where sorts is a list of sort symbols, argument sorts followed by the return sort.
  *)

  RegisterSMTUF "app" sort_lA sort_lA sort_lA.
  (* RegisterSMTUF "rev" sort_lA sort_lA.
  RegisterSMTUF "len" sort_lA sort_Z.
  RegisterSMTUF "tail_rev" sort_lA sort_lA sort_lA. *)

  RegisterSMTFun cons_f "cons" 2.
  RegisterSMTFun nil_f "nil" 0.
  RegisterSMTFun my_app_f "app" 2.
  (* RegisterSMTFun my_rev_f "rev" 1.
  RegisterSMTFun my_len_f "len" 1.
  RegisterSMTFun plus_f "+" 2. *)

  (* Finally we need to handle integer literals *)
  (* RegisterSMTBuiltin z_const_f IntLit. *)

  Transparent denote_tm.
  Require Import MirrorSolve.Axioms.

  Ltac check_goal_unsat := 
    match goal with 
    | |- ?G => check_unsat_neg G; eapply UnsoundAxioms.interp_true
    end.

  Create HintDb list_eqns.

  Hint Resolve app_equation_1 : list_eqns.
  Hint Resolve app_equation_2 : list_eqns.
  (* Hint Resolve rev_equation_1 : list_eqns.
  Hint Resolve rev_equation_2 : list_eqns.
  Hint Resolve len_equation_1 : list_eqns.
  Hint Resolve len_equation_2 : list_eqns. *)

  Ltac prep_proof := 
    hints_foreach (fun x => pose proof x) "list_eqns";
    Utils.revert_all;
    unfold "<->" in *.

  Scheme Equality for fol_sorts.

  Ltac quote_reflect_list := quote_reflect list_sig fm_model fol_sorts_eq_dec match_tacs match_inds.
  Ltac quote_extract_list := quote_extract list_sig fm_model fol_sorts_eq_dec match_tacs match_inds.


  Ltac mirrorsolve :=
    prep_proof;
    quote_reflect_list;
    check_goal_unsat.

  Lemma app_app_one : 
    forall (a: A) (l r : list), 
      app (app l (a :: nil)) r = app l (a :: r).
  Proof.
    induction l; mirrorsolve.
  Qed.
  Hint Immediate app_app_one : list_eqns.

  Lemma app_assoc : 
    forall (x y z: list),
      app (app x y) z = app x (app y z).
  Proof.
    induction x; mirrorsolve.
  Qed.
  Hint Immediate app_assoc : list_eqns.

  Lemma app_nil_r : 
    forall l, app l nil = l.
  Proof.
    induction l; mirrorsolve.
  Qed.
  Hint Immediate app_nil_r : list_eqns.
  
  Notation rev' := ListFuncs.rev.
  
  Lemma rev_app : 
    forall (l r : list), 
     rev' (app l r) = app (rev' r) (rev' l).
  Proof.
    induction l; mirrorsolve.
  Qed.
  Hint Immediate rev_app : list_eqns.

  Lemma rev_rev : 
    forall (l : list), 
      rev' (rev' l) = l.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Lemma rev_rev' : 
    forall (l : list), 
      rev' (rev' l) = l.
  Proof.
    induction l; intros.
    - autorewrite with rev.
      autorewrite with rev.
      trivial.
    - autorewrite with rev.
      erewrite rev_app.
      erewrite IHl.
      autorewrite with rev.
      autorewrite with app.
      trivial.
  Qed.

  Hint Immediate rev_rev : list_eqns.

  Lemma app_len : 
    forall (l r : list), 
      len (app l r) = (len l + len r)%Z.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate app_len : list_eqns.

  Lemma rev_len :
    forall (l: list), 
      len l = len (rev' l).
  Proof.
    induction l; mirrorsolve.
  Qed.

  Lemma rev_len' :
    forall (l: list), 
      len l = len (rev' l).
  Proof.
    induction l.
    - autorewrite with rev.
      trivial.
    - autorewrite with rev.
      autorewrite with len.
      erewrite app_len.
      erewrite IHl.
      autorewrite with len.
      simpl.
      trivial.
  Qed.

End ListFuncs.
  
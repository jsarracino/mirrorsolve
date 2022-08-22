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

(* In this demo we make two different versions of list reverse:
  1) my_rev, which is a naive quadratic list reverse (it uses append at each step, which is linear, on each element of the input)
  2) tail_rev, which is a classic tail-optimized linear list reverse.

  We prove that forall xs, my_rev xs = tail_rev xs using mirrorsolve's proof automation

  To demo the rest of mirrorsolve, we also define a length function, and a custom predicate, and prove properties about them with reverse.
*)

Section ListFuncs.
  Variable (A: Type).

  (* We will make use of a hint database to reflect recursive coq functions into SMT logic.
     For now, don't worry about it, but it's handy to use Equations for recursion to make use of the generated equations.
   *)

  Equations my_app (l: list A) (r: list A) : list A := {
    my_app nil r := r;
    my_app (x :: l') r := x :: my_app l' r;
  }.

  Check my_app_equation_1. (* forall r : list A, my_app [] r = r *)
  Check my_app_equation_2. (* forall (x : A) (l' r : list A), my_app (x :: l') r = x :: my_app l' r *)
  
  Equations my_rev (xs: list A) : list A := {
    my_rev nil := nil;
    my_rev (x :: l') := my_app (my_rev l') [x];
  }.

  Equations tail_rev (xs: list A) (acc: list A) : list A := {
    tail_rev nil acc := acc;
    tail_rev (x :: xs') acc := tail_rev xs' (x :: acc);
  }.

  Equations my_In (x: A) (l: list A) : Prop := {
    my_In x nil := False;
    my_In x (x' :: l') := x = x' \/ my_In x l';
  }.

  Lemma my_In_equation_1' : 
    forall x, ~ my_In x [].
  Proof.
    intros.
    autorewrite with my_In.
    intuition eauto.
  Qed.

  Lemma my_In_equation_2' : 
    forall (x x' : A) (l' : list A),
      my_In x (x' :: l') <-> (x = x' \/ my_In x l').
  Proof.
    intros.
    (* simpl. *)
    autorewrite with my_In.
    intuition eauto.
  Qed.

  (* For simplicity we use Z instead of nat or N, because Z translates directly to SMT. 
     We could also use nat or N and use the N2Z functor to convert goals from nat/N to Z. 
  *)
  Equations my_len (xs: list A) : Z := {
    my_len nil := 0;
    my_len (_ :: xs) := my_len xs + 1;
  }.

  (* Next we set up a first-order logic for lists, my_app, my_rev, tail_rev, my_In, and my_len.
   *)

   Declare ML Module "mirrorsolve".

  Mirror Reflect Add Sort (list A) "list_A".
  Mirror Reflect Add Sort Z.
  Mirror Reflect Add Sort bool.
  Mirror Reflect Add Sort A "A".

  Mirror Reflect Add Sorts.
  Mirror Reflect Add Interp Sorts.

  (* First we need a syntax and semantics for sorts. Our three sorts are A, list A, and Z,
    and we'll need a bool sort for my_In's Prop down the road. *)
  Inductive fol_sorts := sort_A | sort_lA | sort_Z | sort_bool.
  Definition interp_sorts (x: fol_sorts) : Type := 
    match x with 
    | sort_A => A
    | sort_lA => list A
    | sort_Z => Z
    | sort_bool => bool
    end.

  (* Next we define function symbols for everything mentioned in the functions:
    nil, cons, my_app, my_rev, tail_rev, my_len, Z plus, Z constants

    We also define a relation symbol for my_In.

    Our functions and relations have dependent types; functions are indexed by the argument types and return type,
    and relations are indexed by the argument types. The argument types are encoded as a list of fol_sorts symbols.
  
  *)


  Inductive fol_list_funs : list fol_sorts -> fol_sorts -> Type := 
    | nil_f : fol_list_funs [] sort_lA
    | cons_f : fol_list_funs [sort_A; sort_lA] sort_lA
    | my_app_f : fol_list_funs [sort_lA; sort_lA] sort_lA
    | my_rev_f : fol_list_funs [sort_lA] sort_lA
    | tail_rev_f : fol_list_funs [sort_lA; sort_lA] sort_lA
    | my_len_f : fol_list_funs [sort_lA] sort_Z
    | plus_f : fol_list_funs [sort_Z; sort_Z] sort_Z
    | z_const_f : forall (z: Z), fol_list_funs [] sort_Z.

  Inductive fol_list_rels : list fol_sorts -> Type := 
    | my_In_r : fol_list_rels [sort_A; sort_lA].

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
    interp_fun _ _ my_app_f (l ::: r ::: hnil):= my_app l r;
    interp_fun _ _ my_rev_f (x ::: hnil) := my_rev x;
    interp_fun _ _ tail_rev_f (x ::: l ::: hnil) := tail_rev x l;
    interp_fun _ _ my_len_f (x ::: hnil) := my_len x;
    interp_fun _ _ plus_f (l ::: r ::: hnil) := (l + r)%Z;
    interp_fun _ _ (z_const_f z) hnil := z;
  }.
  
  Equations interp_rel args (r: fol_list_rels args) (hargs : HList.t interp_sorts args) : Prop := {
    interp_rel _ my_In_r (x ::: l ::: hnil)  := my_In x l;
  }.

  (* We can wrap these definitions together with the previous signature to get a first-order logic *model* for mirrorsolve! *)

  Program Definition fm_model : model list_sig := {|
    FirstOrder.mod_sorts := interp_sorts;
    FirstOrder.mod_fns := interp_fun;
    FirstOrder.mod_rels := interp_rel;
  |}.


  (* Next we configure the reflection logic for mirrorsolve. 
    So we're going to connect the first-order logic syntax and semantics with Coq's AST in MetaCoq. 
  *)

  (* First we use MetaCoq to get quoted ASTs for the function symbols.
     If a term has implicit arguments (such as nil: forall A, list A),
     we need to quote a coq term that *doesn't* have implicits (for example @nil).
     A safe rule of thumb is to use @ before every quoted term.
  *)

  MetaCoq Quote Definition t_cons := @cons.
  MetaCoq Quote Definition t_nil := @nil.
  MetaCoq Quote Definition t_my_app := @my_app.
  MetaCoq Quote Definition t_my_rev := @my_rev.
  MetaCoq Quote Definition t_tail_rev := @tail_rev.
  MetaCoq Quote Definition t_my_len := @my_len.
  MetaCoq Quote Definition t_plus := @Z.add.
  MetaCoq Quote Definition t_my_In := @my_In.

  (* z constants are handled by a mirrorsolve primitive *)

  (* Next we need boolean tests for checking whether a metacoq AST term is a particular quoted value *)
  Definition is_t_cons t :=  eq_ctor t t_cons.
  Definition is_t_nil t :=  eq_ctor t t_nil.
  Definition is_t_my_app t :=  eq_ctor t t_my_app.
  Definition is_t_my_rev t :=  eq_ctor t t_my_rev.
  Definition is_t_tail_rev t :=  eq_ctor t t_tail_rev.
  Definition is_t_my_len t :=  eq_ctor t t_my_len.
  Definition is_t_plus t :=  eq_ctor t t_plus.
  Definition is_t_my_In t :=  eq_term t t_my_In.

  (* We also need to quote the types: Z, A, and list A *)
  MetaCoq Quote Definition t_Z := (Z).
  MetaCoq Quote Definition t_lA := (@list A).
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
  Definition match_tacs : list ((term -> bool) * tac_syn list_sig fm_model) := [
      ( is_t_my_In, tac_rel_list my_In_r)
    ; ( is_t_cons, tac_fun_list cons_f)
    ; ( is_t_nil, tac_fun_list nil_f)
    ; ( is_t_my_app, tac_fun_list my_app_f)
    ; ( is_t_my_rev, tac_fun_list my_rev_f)
    ; ( is_t_tail_rev, tac_fun_list tail_rev_f)
    ; ( is_t_my_len, tac_fun_list my_len_f)
    ; ( is_t_plus, tac_fun_list plus_f)
    ; ( is_z_term, tac_z_list )
  ].

  (* Analogous reflection matches for sorts *)
  Definition match_inds : list ((term -> bool) * fol_sorts) := [
      (eq_term t_lA, sort_lA)
    ; (eq_term t_A, sort_A)
    ; (eq_term t_Z, sort_Z)
    ; (eq_term t_bool, sort_bool)
  ].

  (* Next we configure the backend SMT plugin. *)

  Declare ML Module "mirrorsolve".

  Mirror Reflect Add Sort (list A) "list_A".
  Mirror Reflect Add Sort Z.
  Mirror Reflect Add Sort bool.
  Mirror Reflect Add Sort A "A".

  Mirror Reflect Add Sorts.
  Mirror Reflect Add Interp Sorts.

  MetaCoq Quote Definition typ := Type.

  Print typ.


  Print sorts.

  (* Prints: 
      Inductive sorts := sorts_Z | sorts_bool | sorts_list.
  *)

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

  RegisterSMTUF "my_app" sort_lA sort_lA sort_lA.
  RegisterSMTUF "my_rev" sort_lA sort_lA.
  RegisterSMTUF "my_len" sort_lA sort_Z.
  RegisterSMTUF "tail_rev" sort_lA sort_lA sort_lA.
  RegisterSMTUF "my_In" sort_A sort_lA sort_bool.

  RegisterSMTFun cons_f "cons" 2.
  RegisterSMTFun nil_f "nil" 0.
  RegisterSMTFun my_app_f "my_app" 2.
  RegisterSMTFun my_rev_f "my_rev" 1.
  RegisterSMTFun tail_rev_f "tail_rev" 2.
  RegisterSMTFun my_len_f "my_len" 1.
  RegisterSMTFun my_In_r "my_In" 2.
  RegisterSMTFun plus_f "+" 2.

  (* Finally we need to handle integer literals *)
  RegisterSMTBuiltin z_const_f IntLit.

  Transparent denote_tm.
  Require Import MirrorSolve.Axioms.

  Ltac check_goal_unsat := 
    match goal with 
    | |- ?G => check_unsat_neg G; eapply UnsoundAxioms.interp_true
    end.

  Create HintDb list_eqns.

  Hint Resolve my_app_equation_1 : list_eqns.
  Hint Resolve my_app_equation_2 : list_eqns.
  Hint Resolve my_rev_equation_1 : list_eqns.
  Hint Resolve my_rev_equation_2 : list_eqns.
  Hint Resolve tail_rev_equation_1 : list_eqns.
  Hint Resolve tail_rev_equation_2 : list_eqns.
  Hint Resolve my_In_equation_1' : list_eqns.
  Hint Resolve my_In_equation_2' : list_eqns.
  Hint Resolve my_len_equation_1 : list_eqns.
  Hint Resolve my_len_equation_2 : list_eqns.

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
    forall (a: A) (l r : list A), 
      my_app (my_app l [a]) r = my_app l (a :: r).
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate app_app_one : list_eqns.

  Lemma app_assoc : 
    forall (x y z: list A),
      my_app (my_app x y) z = my_app x (my_app y z).
  Proof.
    induction x; 
    mirrorsolve.
  Qed.

  Hint Immediate app_assoc : list_eqns.

  SetSMTSolver "z3".

  Lemma my_rev_app : 
    forall (l r : list A), 
     my_rev (my_app l r) = my_app (my_rev r) (my_rev l).
  Proof.
    induction l;
    mirrorsolve.
  Qed.

  Hint Immediate my_rev_app : list_eqns.

  Lemma app_nil_r : 
    forall l, my_app l [] = l.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate app_nil_r : list_eqns.

  Lemma rev_rev : 
    forall (l : list A), 
      my_rev (my_rev l) = l.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate rev_rev : list_eqns.

  Lemma tail_rev_spec : 
    forall (l acc : list A), 
      tail_rev l acc = my_app (my_rev l) acc.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate tail_rev_spec : list_eqns.

  Lemma tail_rev_sound : 
    forall (l : list A), 
      my_rev l = tail_rev l nil.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate tail_rev_sound : list_eqns.

  Lemma app_len : 
    forall (l r : list A), 
      my_len (my_app l r) = (my_len l + my_len r)%Z.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate app_len : list_eqns.

  Lemma rev_len :
    forall (l: list A), 
      my_len l = my_len (my_rev l).
  Proof.
    induction l; mirrorsolve.
  Qed.
  Hint Immediate rev_len : list_eqns.

  Lemma app_In : 
    forall x l r,
      my_In x (my_app l r) <-> my_In x l \/ my_In x r.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate app_In : list_eqns.

  Lemma in_rev : 
    forall x l,
      my_In x l <-> my_In x (my_rev l).
  Proof.
    induction l; mirrorsolve.
  Qed.

End ListFuncs.
  
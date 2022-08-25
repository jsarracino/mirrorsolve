Require Import MirrorSolve.FirstOrder.

Require Import MirrorSolve.BV.
Require Import MirrorSolve.SMT.
Require Import MirrorSolve.UF.

Require Import MirrorSolve.FOList.

Require Import MirrorSolve.HLists.

Import HListNotations.

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
  Unset Universe Polymorphism.

  (* We use a simpler, custom version of lists to make it easier to autogenerate
     plugin configuration. For verification of the same proofs but on normal lists, see tests/Lists.v.
  *)

  Inductive list_A := | nil_A | cons_A : A -> list_A -> list_A.

  Infix "::" := cons_A.
  Notation "[]" := nil_A.

  (* We will make use of a hint database to reflect recursive coq functions into SMT logic.
     For now, don't worry about it, but it's handy to use Equations for recursion to make use of the generated equations.
   *)

  Equations app (l: list_A) (r: list_A) : list_A := {
    app [] r := r;
    app (x :: l') r := x :: app l' r;
  }.

  Check app_equation_1. (* forall r : list A, app [] r = r *)
  Check app_equation_2. (* forall (x : A) (l' r : list A), app (x :: l') r = x :: app l' r *)
  
  Equations rev (xs: list_A) : list_A := {
    rev [] := [];
    rev (x :: l') := app (rev l') (x :: []);
  }.

  Equations tail_rev (xs: list_A) (acc: list_A) : list_A := {
    tail_rev [] acc := acc;
    tail_rev (x :: xs') acc := tail_rev xs' (x :: acc);
  }.

  Equations In (x: A) (l: list_A) : Prop := {
    In x [] := False;
    In x (x' :: l') := x = x' \/ In x l';
  }.

  Lemma In_equation_1' : 
    forall x, ~ In x [].
  Proof.
    intros.
    autorewrite with In.
    intuition eauto.
  Qed.

  Lemma In_equation_2' : 
    forall (x x' : A) (l' : list_A),
      In x (x' :: l') <-> (x = x' \/ In x l').
  Proof.
    intros.
    (* simpl. *)
    autorewrite with In.
    intuition eauto.
  Qed.

  (* For simplicity we use Z instead of nat or N, because Z translates directly to SMT. 
     We could also use nat or N and use the N2Z functor to convert goals from nat/N to Z. 
  *)
  Equations len (xs: list_A) : Z := {
    len [] := 0;
    len (_ :: xs) := len xs + 1;
  }.

  (* Next we set up a first-order logic for lists, app, rev, tail_rev, In, and len.
   *)

  Declare ML Module "mirrorsolve".

  From MetaCoq.Template Require Import All Loader.
  Import MCMonadNotation.

  Require Import MirrorSolve.Config.
  Open Scope bs.

  (* MetaCoq Run (add_sorts ["A"; "lA"; "bool"; "Z"]).
  MetaCoq Run (add_interp_sorts [pack A; pack (list_A); pack bool; pack Z] sorts). *)

  Notation pack x := (existT _ _ x).
  (* Check tmEval. *)

  Universe foo.

  MetaCoq Quote Definition typ_term := Type@{foo}.

  (* TODO: rels, bool, Z and constants *)
  MetaCoq Run (
    add_funs typ_term [
        pack ListFuncs.rev
      ; pack ListFuncs.app
      ; pack ListFuncs.list_A
      ; pack ListFuncs.tail_rev
      ; pack ListFuncs.len
      ; pack Z.add
    ]
  ).

  (* TODO: better names *)

  Notation sort_A := sort_0b0.
  Notation sort_lA := sort_0b1.
  Notation sort_Z := sort_0b10.

  Notation rev_f := f0b0.
  Notation app_f := f0b1.
  Notation nil_f := f0b10.
  Notation cons_f := f0b11.
  Notation tail_rev_f := f0b100.
  Notation len_f := f0b101.
  Notation plus_f := f0b110.
(* 
  Print sorts.
  Print interp_sorts.
  Print fol_funs. *)

  Inductive fol_list_rels : list sorts -> Type := 
    | In_r : fol_list_rels [sort_A; sort_lA].

  (* We package these up into a first-order logic *signature* for lists: the type symbols + function + relation symbols. 
  
  *)
  Definition list_sig: signature := {| 
    sig_sorts := sorts;
    sig_funs := fol_funs;
    sig_rels := fol_list_rels 
  |}.

  (* Next we give a semantics to the function and relation symbols, in terms of the original functions and relation.
    We use equations because the semantics has a dependent type (the sort symbols are interpreted for arguments and results).
    The interpreted arguments are provided in a HList input.
  *)

  Equations interp_fun args ret (f: fol_funs args ret) (hargs : HList.t interp_sorts args) : interp_sorts ret := {
    interp_fun _ _ nil_f _ := [];
    interp_fun _ _ cons_f (x ::: l ::: hnil):= x :: l;
    interp_fun _ _ app_f (l ::: r ::: hnil):= app l r;
    interp_fun _ _ rev_f (x ::: hnil) := ListFuncs.rev x;
    interp_fun _ _ tail_rev_f (x ::: l ::: hnil) := tail_rev x l;
    interp_fun _ _ len_f (x ::: hnil) := len x;
    interp_fun _ _ plus_f (l ::: r ::: hnil) := (l + r)%Z;
    (* interp_fun _ _ (z_const_f z) hnil := z; *)
  }.
  
  Equations interp_rel args (r: fol_list_rels args) (hargs : HList.t interp_sorts args) : Prop := {
    interp_rel _ In_r (x ::: l ::: hnil)  := In x l;
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

  MetaCoq Quote Definition t_cons := @ListFuncs.cons_A.
  MetaCoq Quote Definition t_nil := @ListFuncs.nil_A.
  MetaCoq Quote Definition t_app := @ListFuncs.app.
  MetaCoq Quote Definition t_rev := @ListFuncs.rev.
  MetaCoq Quote Definition t_tail_rev := @tail_rev.
  MetaCoq Quote Definition t_len := @ListFuncs.len.
  MetaCoq Quote Definition t_plus := @Z.add.
  MetaCoq Quote Definition t_In := @ListFuncs.In.

  (* TODO Z constants *)

  (* Next we need boolean tests for checking whether a metacoq AST term is a particular quoted value *)
  Definition is_t_cons t :=  eq_ctor t t_cons.
  Definition is_t_nil t :=  eq_term t t_nil.
  Definition is_t_app t :=  eq_ctor t t_app.
  Definition is_t_rev t :=  eq_ctor t t_rev.
  Definition is_t_tail_rev t :=  eq_ctor t t_tail_rev.
  Definition is_t_len t :=  eq_ctor t t_len.
  Definition is_t_plus t :=  eq_ctor t t_plus.
  Definition is_t_In t :=  eq_term t t_In.

  (* We also need to quote the types: Z, A, and list A *)
  MetaCoq Quote Definition t_Z := (Z).
  MetaCoq Quote Definition t_lA := (list_A).
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

  (* List of reflection matches; the first element is a test function and the second is a conversion tactic to apply.
   *)
  Definition match_tacs : list ((term -> bool) * tac_syn list_sig fm_model) := [
      ( is_t_In, tac_rel_list In_r)
    ; ( is_t_cons, tac_fun_list cons_f)
    ; ( is_t_nil, tac_fun_list nil_f)
    ; ( is_t_app, tac_fun_list app_f)
    ; ( is_t_rev, tac_fun_list rev_f)
    ; ( is_t_tail_rev, tac_fun_list tail_rev_f)
    ; ( is_t_len, tac_fun_list len_f)
    ; ( is_t_plus, tac_fun_list plus_f)
  ].

  (* Analogous reflection matches for sorts *)
  Definition match_inds : list ((term -> bool) * sorts) := [
      (eq_term t_lA, sort_lA)
    ; (eq_term t_A, sort_A)
    ; (eq_term t_Z, sort_Z)
    (* ; (eq_term t_bool, sort_bool) *)
  ].


  (* The section variable A is an uninterpreted sort in SMT. *)
  RegisterCustomSort sort_A "A".

  (*  The inductive sort list A maps to an inductive smt sort,
      specified as a sum (coq list) of products (also a coq list),
      with cons and nil constructors.
  *)
  RegisterSMTInd sort_lA (SICases [
      ("cons"%string, [SISort (SCustom "A"); SIRec]%list) (* This declares an smt constructor named cons with an "A" argument and a recursive argument (i.e. the inner list) *)
    ; ("nil"%string, nil) (* This declares an smt constructor named nil with no arguments *)
  ]) "A_list".

  (* Map the Z sort to SMT Int, and the bool sort to SMT bool *)
  RegisterSMTSort sort_Z SInt.
  (* RegisterSMTSort sort_bool SBool. *)

  (* The inductive declaration puts "cons" and "nil" in scope as SMT function symbols, 
    but the rest of our functions/relations still need to be declared. 
    We do this with the RegisterSMTUF vernacular. 
    The syntax for this vernacular is:

    RegisterSMTUF "<function name>" sorts.

    where sorts is a list of sort symbols, argument sorts followed by the return sort.
  *)

  RegisterSMTUF "app" sort_lA sort_lA sort_lA.
  RegisterSMTUF "rev" sort_lA sort_lA.
  RegisterSMTUF "len" sort_lA sort_Z.
  RegisterSMTUF "tail_rev" sort_lA sort_lA sort_lA.
  (* RegisterSMTUF "In" sort_A sort_lA sort_bool. *)

  RegisterSMTFun cons_f "cons" 2.
  RegisterSMTFun nil_f "nil" 0.
  RegisterSMTFun app_f "app" 2.
  RegisterSMTFun rev_f "rev" 1.
  RegisterSMTFun tail_rev_f "tail_rev" 2.
  RegisterSMTFun len_f "len" 1.
  (* RegisterSMTFun In_r "In" 2. *)
  RegisterSMTFun plus_f "+" 2.

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
  Hint Resolve rev_equation_1 : list_eqns.
  Hint Resolve rev_equation_2 : list_eqns.
  Hint Resolve tail_rev_equation_1 : list_eqns.
  Hint Resolve tail_rev_equation_2 : list_eqns.
  (* Hint Resolve In_equation_1' : list_eqns.
  Hint Resolve In_equation_2' : list_eqns. *)
  (* Hint Resolve len_equation_1 : list_eqns.
  Hint Resolve len_equation_2 : list_eqns. *)

  Ltac prep_proof := 
    hints_foreach (fun x => pose proof x) "list_eqns";
    Utils.revert_all;
    unfold "<->" in *.

  Scheme Equality for sorts.

  Ltac quote_reflect_list := quote_reflect list_sig fm_model sorts_eq_dec match_tacs match_inds.
  Ltac quote_extract_list := quote_extract list_sig fm_model sorts_eq_dec match_tacs match_inds.

  Ltac mirrorsolve :=
    prep_proof;
    quote_reflect_list;
    check_goal_unsat.

  Lemma app_app_one : 
    forall (a: A) (l r : list_A), 
      app (ListFuncs.app l (a::[])) r = app l (a :: r).
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate app_app_one : list_eqns.

  Lemma app_assoc : 
    forall (x y z: list_A),
      app (app x y) z = app x (app y z).
  Proof.
    induction x; 
    mirrorsolve.
  Qed.

  Hint Immediate app_assoc : list_eqns.

  SetSMTSolver "z3".

  Lemma rev_app : 
    forall (l r : list_A), 
      ListFuncs.rev (app l r) = app (ListFuncs.rev r) (ListFuncs.rev l).
  Proof.
    induction l;
    mirrorsolve.
  Qed.

  Hint Immediate rev_app : list_eqns.

  Lemma app_nil_r : 
    forall l, app l [] = l.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate app_nil_r : list_eqns.

  Lemma rev_rev : 
    forall (l : list_A), 
      ListFuncs.rev (ListFuncs.rev l) = l.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate rev_rev : list_eqns.

  Lemma tail_rev_spec : 
    forall (l acc : list_A), 
      tail_rev l acc = ListFuncs.app (ListFuncs.rev l) acc.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate tail_rev_spec : list_eqns.

  Lemma tail_rev_sound : 
    forall (l : list_A), 
      ListFuncs.rev l = tail_rev l [].
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate tail_rev_sound : list_eqns.

  Lemma app_len : 
    forall (l r : list_A), 
      len (app l r) = (len l + len r)%Z.
  Proof.
    (* induction l; mirrorsolve. *)
  Admitted.

  Hint Immediate app_len : list_eqns.

  Lemma rev_len :
    forall (l: list_A), 
      len l = len (ListFuncs.rev l).
  Proof.
    induction l; mirrorsolve.
  Qed.
  
  Hint Immediate rev_len : list_eqns.

  Lemma app_In : 
    forall x l r,
      In x (app l r) <-> In x l \/ In x r.
  Proof.
    (* induction l; mirrorsolve. *)
  Admitted.

  Hint Immediate app_In : list_eqns.

  Lemma in_rev : 
    forall x l,
      In x l <-> In x (ListFuncs.rev l).
  Proof.
    (* induction l; mirrorsolve. *)
  Admitted.

End ListFuncs.
  
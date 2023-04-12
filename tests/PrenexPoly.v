From elpi Require Import elpi.

Elpi Db types.db lp:{{ 
  pred types o:term.
}}.

Elpi Command get_types.
Elpi Accumulate Db types.db.
Elpi Accumulate lp:{{
  pred setly o:term.
  setly X :- types X, coq.typecheck X Ty ok, Ty = {{ Set }}.
  main [] :- 
    std.findall (setly _) LS,
    coq.say "The current set of setly types is" LS.
}}.
Elpi Typecheck.

Elpi Command add_type.
Elpi Accumulate Db types.db.
Elpi Accumulate lp:{{
  main [trm Trm] :- 
    coq.elpi.accumulate _ "types.db" 
      (clause _ _ (types Trm)).
}}.
Elpi Typecheck.

Elpi add_type (nat).
Elpi add_type (list).
Elpi add_type (True).
Elpi add_type (list nat).
Elpi get_types.
(* prints [types global indt «nat», types global indt «list»] *)

Require Import Coq.Lists.List.
Import ListNotations.

From Equations Require Import Equations.

Section ExtensibleTypes.

  Inductive list_idx {A: Type} : list A -> Type := 
    | LIHere : 
      forall x {xs}, 
        list_idx (x :: xs)
    | LIThere : 
      forall {x xs}, 
        list_idx xs -> 
        list_idx (x :: xs).

  Equations get_idx {A} {xs: list A} (key: list_idx xs) : A := 
  {
    get_idx (LIHere v) := v;
    get_idx (LIThere i) := get_idx i;
  }.

  Equations eqb {A A'} {xs : list A} {xs' : list A'} (l : list_idx xs) (r: list_idx xs') : bool := 
  {
    eqb (LIHere _) (LIHere _) := true;
    eqb (LIThere l) (LIThere r) := eqb l r;
    eqb _ _ := false;
  }.

  Require Import Coq.Program.Equality.

  Lemma idx_inj : 
    forall A x (xs: list A) (l r: list_idx xs), 
      LIThere (x := x) l = LIThere (x := x) r <-> l = r.
  Proof.
    intros.
    split; intros.
    - inversion H.
      inversion_sigma.
      subst.
      simpl in *.
      unfold eq_rect in *.
      revert H.
      revert H1_.
  Admitted.

  
  Lemma eqb_eq : 
    forall A (xs: list A) (l r: list_idx xs), 
      eqb l r = true <-> l = r.
  Proof.
    induction xs;
    intros; try now inversion l.
    dependent destruction l;
    dependent destruction r;
    autorewrite with eqb.
    - split; intros; trivial.
    - split; intros H; inversion H.
    - split; intros H; inversion H.
    - erewrite IHxs.
      split; intros.
      + subst; trivial.
      + eapply idx_inj.
        eauto.
  Qed.

  Require Import Coq.Classes.EquivDec.
  (* Definition eqdec_all {A} {xs: list A} : EqDec (list_idx xs) eq.
  refine (
    (fix comp_eqd xs' := _ ) xs
  ). *)
 (* Local Obligation Tactic := intros; try now congruence.  *)
  Equations eqdec_all {A:Type} {xs: list A} : EqDec (list_idx xs) eq := {
    eqdec_all (LIHere _) (LIHere _) := left eq_refl;
    eqdec_all (LIThere l') (LIThere r') with eqdec_all l' r' := {
      eqdec_all (LIThere l') (LIThere r') (left _) := left _;
      eqdec_all (LIThere l') (LIThere r') (right _) := right _;
    } ;
    eqdec_all (LIThere _) (LIHere _) := right _;
    eqdec_all (LIHere _) (LIThere _) := right _;
  }.
  Next Obligation.
  Defined.
  Next Obligation.
    eapply c.
    dependent induction H1.
    trivial.
  Defined.

  Variable (sorts_lst: list Set).
  Definition sorts := list_idx sorts_lst.

  Definition interp_sorts (s: sorts) := get_idx s.

  (* Inductive funs : list sorts -> sorts -> Type := . *)

  Require Import MirrorSolve.HLists.

  Fixpoint func_ty (args: list sorts) (ret: sorts): Type := 
    match args with 
    | nil => get_idx ret
    | t :: ts => (get_idx t -> (func_ty ts ret))%type
    end.

  Definition funs args ret := func_ty args ret.

  Import HListNotations.

  Local Obligation Tactic := intros.

  Equations apply_args_f args ret (f: funs args ret) (hargs: HList.t interp_sorts args) : interp_sorts ret by struct hargs := 
  {
    apply_args_f _ _ v hnil := v;
    apply_args_f _ _ f (v ::: vs) := apply_args_f _ _ (f v) vs;
  }.

  Definition mod_funs : 
    forall args ret,
      funs args ret ->
      HList.t interp_sorts args ->
      interp_sorts ret := 
    fun _ _ f hl => apply_args_f _ _ f hl.

  Fixpoint rel_ty (args: list sorts): Type := 
    match args with 
    | nil => Prop
    | t :: ts => (get_idx t -> (rel_ty ts))%type
    end.
  
  Definition rels args := rel_ty args.

  Equations apply_args_r args (r: rels args) (hargs: HList.t interp_sorts args) : Prop by struct hargs := 
    {
      apply_args_r _ v hnil := v;
      apply_args_r _ f (v ::: vs) := apply_args_r _ (f v) vs;
    }.

  Definition mod_rels' : 
    forall args,
      rels args ->
      HList.t interp_sorts args ->
      Prop := 
    fun _ r hl => apply_args_r _ r hl.

  Require Import MirrorSolve.FirstOrder.

  Definition sig_extensible : signature := {|
    sig_sorts := sorts;
    sig_funs := fun args ret => funs args ret;
    sig_rels := fun args => rels args;
  |}.

  Program Definition mod_extensible : model sig_extensible := {|
    mod_sorts := interp_sorts;
    mod_fns := mod_funs;
    mod_rels := mod_rels';
  |}.

End ExtensibleTypes.

Arguments LIHere {_ _ _}.

Definition tys_list : list Set := [nat ; bool ; list nat ].

Definition nat_idx : list_idx tys_list := LIHere.
Definition bool_idx : list_idx tys_list := LIThere (LIHere).

Definition add_func : funs _ [nat_idx; nat_idx] nat_idx := Nat.add.
Require Import MirrorSolve.Reflection.Tactics.


Notation sig := (sig_extensible tys_list).
Notation mod := (mod_extensible tys_list).

Definition sorts_eq_dec :  EquivDec.EqDec (sig_sorts sig) eq := eqdec_all.

(* 
  This is the reflection theorem for converting Coq Props (as quoted terms) to interpretations of FOL terms.
  The brittle part has been sig and mod -- we've been using bespoke inductive types so far.
  *)
Check @denote_extract_specialized_rev sig mod sorts_eq_dec.

Eval vm_compute in sorts_eq_dec bool_idx bool_idx.


(* let's do the following goal: 
   forall {A} (xs: list A), 
    app' xs [] = xs 

  (where app' is list append)
*)

Fixpoint app' {A: Type} (xs ys : list A) :=  
  match xs with 
  | [] => ys
  | x :: xs => x :: app' xs ys
  end.

Elpi Tactic mirrorsolve.
Elpi Accumulate lp:{{

  pred setly i: term.
  setly X :- coq.say "setly with" X, fail.
  setly X :- coq.typecheck X Ty ok, Ty = {{ Set }}.
  setly X :- coq.typecheck X Ty ok, Ty = {{ Type }}.

  pred add_all i: list term i: std.set term o: std.set term.
  add_all [] O O.
  add_all [T|TS] S O :- 
    add_all TS S O', 
    std.set.add T O' O.

  pred union_all i: list (std.set term) o: std.set term.
  union_all [] O :- std.set.make _ O.
  union_all [S|SS] O :- 
    union_all SS O', 
    add_all T O' O.

  pred union i:std.set term i:std.set term o: std.set term.
  union L R O :- 
    std.set.elements L LS,
    add_all LS R O.

  pred gather_sorts_ls i: list term o: std.set term.
  gather_sorts_ls [] O :- std.set.make _ O.
  gather_sorts_ls [T|TS] O :- 
    coq.say "recursing on term" T,
    gather_sorts T O'',
    gather_sorts_ls TS O',
    union O'' O' O.

  pred single i:term o: std.set term.
  single X _ :- coq.say "singleton with" X, fail.
  single X O :- 
    std.set.make _ Empty,
    std.set.add X Empty O. 
  pred gather_sorts_term i: term o: std.set term.
  gather_sorts_term T O :- setly T, coq.say T "is setly", single T O.
  gather_sorts_term T O :- coq.say T "is not setly", std.set.make _ O.


  pred gather_sorts i:term o:std.set term.
  gather_sorts (app TS as G) GO :- 
    gather_sorts_term G GO', 
    gather_sorts_ls TS GO'',
    union GO' GO'' GO.
  gather_sorts G GO :- gather_sorts_term G GO.

  pred setly_evar i: prop o:std.set term.
  setly_evar X _ :- coq.say "setly_evar with" X, fail.
  setly_evar (decl X _ _) O :- setly X, single X O.
  setly_evar _ O :- std.set.make _ O.

  pred setly_evars i: list prop o: std.set term.
  setly_evars X _ :- coq.say "setly_evars with" X, fail.
  setly_evars [] O :- std.set.make _ O.
  setly_evars [X|XS] O :- 
    setly_evar X O',
    setly_evars XS O'',
    union O' O'' O.

  solve (goal Vs _ G' _ _ as G) GL :- 
    % gather_sorts G' O,
    % gather_sorts G' O, 
    % std.set.elements O LS,
    % gather_sorts G' O, 
    setly_evars Vs O,
    % std.set.cardinal O N,
    std.set.elements O L,

    coq.say "the evars are" Vs "and the setly vars are" L.
}}.
Elpi Typecheck.

Ltac mirrorsolve' := admit.

(* Elpi Trace.  *)
Lemma app'_nil_r: 
  forall {A} (xs: list A), app' xs [] = xs.
Proof.
  intros.
  elpi mirrorsolve. (* for sorts, we expect A, list A *)
  (* ideally the following proof: *)
  induction xs; mirrorsolve'.
Admitted.
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

(* theory:
  list :: * -> *
  nat :: *

  list = 
    | nil: forall X, list X 
    | cons : forall X, X -> list X -> X

  app :: forall X, list X -> list X -> list X
  app_0: forall X (xs: list X), app nil xs = xs
  app_1: forall X (x: X) (xs ys: list X), app (x :: xs) ys = x :: app xs ys

query:
  " A : Type
    ========================
    5 = length (xs: list A)"
  step 0: types are nat, list nat *)

(* Locate Z. *)

Require Import MirrorSolve.SMT.

Elpi Db theory.db lp:{{ 
  kind kind_expr type.  

  type kind_star kind_expr.
  type kind_arr kind_expr -> kind_expr -> kind_expr.

  kind sorts_info type.
  pred ind_info i: term o:int o: list constructor o: list term.
  ind_info (global (indt Ind)) Arity CNames CTypes :- 
    coq.env.indt Ind tt Arity _ _ CNames CTypes.

  pred sorts i:term, o: kind_expr.
  sorts ({{ nat }}) kind_star.
  sorts ({{ BinNums.Z }}) kind_star.
  sorts ({{ bool }}) kind_star.
  sorts (global (indt Ind)) (kind_arr kind_star kind_star) :- 
    coq.env.indt Ind tt 1 _ _ _ _.
  
  % tuple up the constructor names as strings with their types
  % for the types, we need to resolve the 

  pred builtin_sorts i: term, o: term.
  builtin_sorts {{ nat }} {{ SInt }}.

  kind concrete_sort type.  
  type concrete_base term -> concrete_sort.
  type concrete_par name -> concrete_sort.
  type concrete_app concrete_sort -> list concrete_sort -> concrete_sort.

  pred gen_smt_sort i: concrete_sort, o: term.
  gen_smt_sort (concrete_base T) Out :- 
    sorts T kind_star,
    builtin_sorts T Out.
  gen_smt_sort (concrete_app Ind Arg) Out :- 
    sorts Ind (kind_arr kind_star kind_star),
    ind_info Ind 1 CNames CTypes,
    % TODO: connect the concrete argument with the constructor names and types,
    % make a name (string) for the inductive and also the constructors,
    % instantiate the constructors with the arguments,
    % tuple everything up into an SMT.smt_ind term for Out.


}}.
Elpi Typecheck.

Elpi Command Add_Ind.
Elpi Accumulate Db theory.db.
Elpi Accumulate lp:{{
  main [trm Trm] :- 
    coq.elpi.accumulate _ "theory.db" 
      (clause _ _ (sorts Trm (kind_arr kind_star kind_star))).
}}.
Elpi Typecheck.

Elpi Add_Ind (list).

Elpi Command Print_sort.
Elpi Accumulate Db theory.db.
Elpi Accumulate lp:{{
  main [trm Trm] :- 
    gen_smt_sort (concrete_base Trm) Out, 
    coq.say Out.
}}.
Elpi Typecheck.

Elpi Print_sort (list).


Elpi Tactic mirrorsolve.
Elpi Accumulate lp:{{

  pred setly i: term.
  % setly X :- coq.say "setly with" X, fail.
  setly X :- coq.typecheck X Ty ok, Ty = {{ Set }}.
  setly X :- coq.typecheck X Ty ok, Ty = {{ Type }}.



  typeabbrev kind_ctx (list (pair term kind_expr)).

  pred ctx-empty o: kind_ctx.
  % ctx-empty O :- std.map.make _ O.
  ctx-empty [].

  pred ctx-add i: term, i: kind_expr, i: kind_ctx, o: kind_ctx.
  % ctx-add K V O' O :- std.map.add K V O' O.
  ctx-add K V O' [pr K V|O'].

  pred ctx-single i: term, i: kind_expr, o: kind_ctx.
  ctx-single K V O :- 
    ctx-empty O,
    ctx-add K V O' O.

  pred ctx-mapsto i: kind_ctx, i: term, o: kind_expr.
  % ctx-mapsto Ctx K V :- coq.say "ctx-mapsto" Ctx K V, fail.
  % ctx-mapsto Ctx K V :- std.map.find K Ctx V.
  ctx-mapsto Ctx K V :- std.lookup Ctx K V.

  pred mk-decl i: prop, o: term, o: kind_expr.
  mk-decl (decl Var Name _) Var (kind_par Name) :- setly Var.

  % TODO: there's probably a way to write this with std.list functions
  pred mk-decls i: list prop o: kind_ctx.
  mk-decls [] O :- ctx-empty O.
  mk-decls [D|DS] O :- 
    mk-decl D K V, !,
    mk-decls DS O', 
    ctx-add K V O' O.
  mk-decls [_|DS] O :- mk-decls DS O.

  % set helper functions

  typeabbrev kind_expr_set (list kind_expr).
  % empty set
  pred set-empty o: kind_expr_set.
  % set-empty O :- std.set.make _ O.
  set-empty [].

  % single element
  pred set-single i:kind_expr o: kind_expr_set.
  % set-single X _ :- coq.say "set-single" X, fail.
  % set-single X O :- 
  %   set-empty Empty, !,
  %   std.set.add X Empty O.
  set-single X [X].

  pred set-add i: kind_expr, i: kind_expr_set, o: kind_expr_set.
  set-add X S S :- std.mem S X.
  set-add X S [X|S].

  % combine a list and a set into a set
  pred add-all i: list kind_expr, i: kind_expr_set, o: kind_expr_set.
  add-all [] O O.
  add-all [T|TS] S O :- 
    add-all TS S O', 
    set-add T O' O.

  pred set-elems i: kind_expr_set, o: list kind_expr.
  set-elems X X.

  % union two sets together
  pred union i:kind_expr_set, i:kind_expr_set, o: kind_expr_set.
  union L R O :- 
    set-elems L LS,
    add-all LS R O.

  % flatten a list of sets into a single set 
  pred flatten i: list (kind_expr_set), o: kind_expr_set.
  % flatten X _ :- coq.say "flatten" X, fail.
  flatten [] O :- set-empty O.
  flatten [S|SS] O :- 
    flatten SS O', 
    union S O' O.

  % base case: convert an atomic term into a kind_expr if it is in the context
  pred sortify_term i: kind_ctx, i: term, o: kind_expr.
  sortify_term Ctx T O :- ctx-mapsto Ctx T O.
  sortify_term Ctx (app [T|TS] as T') (kind_app O TSO) :-
    setly T',
    sortify_term Ctx T O,
    std.map TS (sortify_term Ctx) TSO.
  sortify_term Ctx (app [T|TS] as T') (kind_app (kind_base T) TSO) :-
    setly T',
    std.map TS (sortify_term Ctx) TSO.

  % lift sortify_term to sets
  pred gather_sorts_term i: kind_ctx, i: term, o: kind_expr_set.
  % gather_sorts_term Ctx T O :- coq.say "gather_sorts_term" Ctx T O, fail.
  gather_sorts_term Ctx T O :-
    sortify_term Ctx T KE,
    set-single KE O.
  gather_sorts_term _ _ O :- set-empty O.

  % Coq's AST roughly represents the Coq Type 
  % prod nat (list nat) (i.e. nat * list nat):
  % (app prod [nat; (app list [nat])])
  % Elpi represents the same type as:
  % (app [prod; nat; (app [list; nat])])


  pred gather_sorts i: kind_ctx, i:term, o:kind_expr_set.
  % gather_sorts Ctx G O :- coq.say "gather_sorts" Ctx G O, fail.
  gather_sorts Ctx (app TS as G) O :- 
    gather_sorts_term Ctx G O', 
    std.map-filter TS (gather_sorts Ctx) TO,
    flatten TO O'',
    union O' O'' O.
  gather_sorts Ctx G O :- gather_sorts_term Ctx G O.

  % forall (X: Type), list X = list X
  % intros ===>

  % X: Type 
  % =========
  % list X = list X

  solve (goal Ctx _ G' _ _ as G) GL :- 
    coq.say "CTX is:" Ctx,
    mk-decls Ctx CtxMap,
    coq.say "the names are" CtxMap,
    gather_sorts CtxMap G' KEs,
    coq.say "the kind exprs are" KEs.
}}.
Elpi Typecheck.

Ltac mirrorsolve' := admit.

Lemma app'_nil_r: 
  forall {A} (xs: list A), app' xs [] = xs.
Proof.
  intros.
  elpi mirrorsolve. (* for sorts, we expect A, list A *)
  (* ideally the following proof: *)
  induction xs; mirrorsolve'.
Admitted.
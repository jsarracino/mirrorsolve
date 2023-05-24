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
  app_,: forall X (xs: list X), app nil xs = xs
  app_1: forall X (x: X) (xs ys: list X), app (x :: xs) ys = x :: app xs ys

query:
  " A : Type
    ========================
    5 = length (xs: list A)"
  step 0: types are nat, list nat *)

(* Locate Z. *)

Require Import MirrorSolve.SMT.

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Locate Z.

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

  pred ind->name i: indt-decl, o: string.
  % Note: for parameters, we don't actually care what the HOAS is applied to, so we pass it a term on hand (in this case the type of the parameter)
  ind->name (parameter _ _ X FI) Out :- ind->name (FI X) Out.
  ind->name (inductive Nme _ _ _) Nme.

  % list : forall (A: Set), Type
  %   (| cons | nil : list A)

  % parameter _ "A" Set (fun A => | cons A | nil : list A)

  pred sort->smt_name i: term, o: string.
  % primitive types
  sort->smt_name {{ nat }} "Z".
  sort->smt_name {{ BinNums.Z }} "Z".
  sort->smt_name {{ bool }} "Bool".
  % inductive types
  sort->smt_name (global (indt Ind)) Nme :- 
    coq.env.indt-decl Ind Ind-decl,
    ind->name Ind-decl Nme.
  % type application
  sort->smt_name (app [F|Args]) Out :- 
    std.map Args sort->smt_name OArgs, 
    sort->smt_name F FO, 
    std.string.concat "_" OArgs ArgsCat,
    Out is FO ^ "_" ^ ArgsCat.
  % parametric types (encoded as SCustoms) TODO
  % sort->smt_name {{ SCustom lp:Nme }} Nme.

  % convert a sort to an SMT sort
  pred sort->smt i: term, o: term.
  sort->smt {{ nat }} {{ SInt }}.
  sort->smt {{ BinNums.Z }} {{ SInt }}.
  sort->smt {{ bool }} {{ SBool }}.
  % inductive types
  sort->smt (global (indt Ind)) {{ SCustom lp:Nme }} :- 
    coq.env.indt-decl Ind Ind-decl,
    ind->name Ind-decl NmeStr,
    str->term NmeStr Nme.

  % (Z + (Z + Z)) ===> sum_Z_sum_Z_Z

  % type application
  sort->smt (app [F|Args]) {{ SCustom lp:Nme }} :- 
    std.map Args sort->smt_name OArgs, 
    sort->smt_name F FO, 
    std.string.concat "_" OArgs ArgsCat,
    NmeStr is FO ^ "_(" ^ ArgsCat ^ ")",
    % TODO: check this if SMT sorts can't have parens
    str->term NmeStr Nme.
  % parametric types (encoded as SCustoms )
  sort->smt {{ SCustom lp:Nme }} {{ SCustom lp:Nme }}.
  sort->smt {{ SIRec }} {{ SIRec }}.


  % translating a constructor to a Coq term
  pred ctor->term i: indc-decl, o: term.
  ctor->term (constructor _ A) O :- coq.arity->term A O.

  pred term->ind i: term, o: indt-decl.
  term->ind (global (indt Ind)) O :- coq.env.indt-decl Ind O.

  % converts a inductive application to a list of terms corresponding to the constructors with the overall inductive application as the recursive type
  % e.g. list A ===> [nil: list A, cons : A -> list A -> list A]
  pred app_ctors i: indt-decl, i: term, i: list term, i: list term, o: list term.
  app_ctors (parameter _ _ _ I) Self Args [Arg|Args'] Out :- 
    app_ctors (I Arg) Self [Arg|Args] Args' Out.
  app_ctors (inductive _ _ _ Ctors) Self Args [] Out :- 
    std.rev Args Args',
    coq.say "reduced self to" (app [Self|Args']), 
    std.map (Ctors (app [Self|Args'])) ctor->term Out.

  pred ctor->term i: indc-decl, o: term.
  ctor->term (constructor _ A) O :- coq.arity->term A O.

  % similar logic as above but replaces the recursive type with SRec. Notice that these constructors are not well-typed as coq terms.
  %  e.g. list Z ===> [nil: SRec, cons : Z -> SRec -> SRec]
  pred app_ctors_smt i: indt-decl, i: list term, o: term.
  app_ctors_smt (parameter _ _ _ I) [Arg|Args] Out :- 
    app_ctors_smt (I Arg) Args Out.
  app_ctors_smt (inductive _ _ _ Ctors) [] {{ SICases lp:CtorTys' }} :- 
    std.map (Ctors {{ SIRec }}) ctor->smt CtorTys,
    l2c CtorTys CtorTys'.

  pred l2c i: list term, o: term.
  l2c [] {{ [] }}.
  l2c [X|XS] {{lp:X :: lp:R}} :- 
    l2c XS R.


  % lift terms of smt_sort_base to smt_ind_base, skipping over SIRec when present
  pred lift_smt_sort i: term, o: term.
  lift_smt_sort {{ SIRec }} {{ SIRec }}.
  lift_smt_sort T {{ SISort lp:T }}.


  pred ctor->smt i: indc-decl, o: term.
  ctor->smt (constructor Nme Arity) {{ (lp:CoqName, lp:CtorType') }} :- 
    str->term Nme CoqName,
    coq.arity->term Arity T,
    ctor_type->smt T CtorType,
    l2c CtorType CtorType'.

  % Z -> SIRec -> SRec    ===> 
  % [SInt, SIRec]

  pred ctor_type->smt i: term, o: list term.
  ctor_type->smt {{ SIRec }} [].
  ctor_type->smt (prod _ Ty FI) [Srt|Rec] :-
    sort->smt Ty Inter,
    lift_smt_sort Inter Srt,
    % it should be the case that forall T T', FI T = FI T' (i.e. this is an anonymous prod),
    % so we pass the type as a dummy term
    ctor_type->smt (FI Ty) Rec.
  


  % list nat starts as 
  %            (forall T, | nil : T, | cons : A -> T -> T) nat
  %          =apply= 
  %             | nil : list nat, | cons : nat -> list nat -> list nat
  %          =map sort->smt over anonymous products= 
  %             | nil : SRec, | cons : Z -> SRec -> SRec
  %          =convert anonymous products to SMT sort inductive=
  %             |  



  % pred arity->smt_tys i: term, o: list term.
  % ctor->smt (prod `_` Ty FI) 
  % end inductive translation

  % reflecting an elpi string to a Coq String.String
  pred dig->bit i: int, o: bool.
  dig->bit 0 ff.
  dig->bit 1 tt.

  pred int->bits_h i:int, o: list bool.
  int->bits_h X [Bit] :- dig->bit X Bit.
  int->bits_h X [Dig|XS] :- 
    LSB is X mod 2,
    dig->bit LSB Dig,
    Rem is X div 2,
    int->bits_h Rem XS.

  pred repeat i: bool, i: int, o: list bool.
  repeat _ 0 [].
  repeat X N [X|XS] :- 
    N > 0, 
    M is N - 1,
    repeat X M XS.

  pred int->bits i: int, o: list bool.
  int->bits X XS :- 
    int->bits_h X Digs,
    std.length Digs N,
    M is 8 - N,
    repeat ff M Suffix, 
    std.append Digs Suffix XS.

  pred bit->cbool i:bool, o: term.
  bit->cbool tt {{ true }}.
  bit->cbool ff {{ false }}.

  pred bits->ascii i: list bool, o: term.
  bits->ascii Bs Out :- 
    std.map Bs bit->cbool CArgs,
    % coq.say CArgs,
    Out = app [{{ Ascii }} | CArgs].

  pred int->ascii i: int, o: term.
  int->ascii X O :- 
    int->bits X Bits,
    bits->ascii Bits O.

  pred str->chars i: string, o: list string.
  str->chars X [X] :- 
    N is size X,
    N = 1.
  str->chars X [C|XS] :- 
    N is (size X) - 1,
    Y is substring X 1 N, 
    str->chars Y XS,
    C is substring X 0 1.

  pred chr->term i: string, o: term.
  chr->term C Out :- 
    CV is rhc C,
    int->ascii CV Out.

  pred make_str i: list term, o: term.
  make_str [] {{ EmptyString }}.
  make_str [C|CS] (app [CTor,C,R]) :- 
    make_str CS R,
    CTor = {{ String }}.

  % output term is a Coq term for a Strings.String.
  pred str->term i: string, o: term.
  str->term Str Out :- 
    str->chars Str Chrs,
    std.map Chrs chr->term Asciis, 
    make_str Asciis Out.

  % end string reflection

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

(* Elpi Add_Ind (list). *)

Elpi Command Print_sort.
Elpi Accumulate Db theory.db.
Elpi Accumulate lp:{{
  main [trm (app [(global (indt F))|Args])] :- 
    coq.env.indt-decl F FI,
    app_ctors_smt FI Args Out,
    coq.say "smt ctor types are:" Out.
}}.
Elpi Typecheck.



Elpi Print_sort ((list nat)%type).


(* Code below here doesn't work, needs to be adapted to make (and use) sort->smt etc *)

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
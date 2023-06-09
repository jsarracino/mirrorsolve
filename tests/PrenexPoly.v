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
  % sort->smt_name {{ SCustom lp:NmeStr }} Nme :- 
  %   str->term Nme NmeStr.
  sort->smt_name {{ SCustom lp:NmeStr }} Out :- 
    coq.say "Name is" NmeStr,
    Out = "A",
    coq.say "Output is" Out.

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
Elpi Accumulate Db theory.db.
Elpi Accumulate lp:{{

  % replace prenex parameter type variables with scustom type variables in a term
  pred replace_abs_sorts i: term, o: term.
  replace_abs_sorts (prod Nme {{ Type }} FT) Out :- 
    coq.name->id Nme NmeStr,
    str->term NmeStr CoqNme,
    replace_abs_sorts (FT {{ SCustom lp:CoqNme }}) Out.
  replace_abs_sorts (prod Nme {{ Set }} FT) Out :- 
    coq.name->id Nme NmeStr,
    str->term NmeStr CoqNme,
    replace_abs_sorts (FT {{ SCustom lp:CoqNme }}) Out.
  replace_abs_sorts T T.


  % uses_fun {{ app xs [] }} {{ app }} {{ list <A> -> list <A> -> list <A> }}

  % app' : forall (A: Type) (_: list A) (_: list A), list A
  % @app' (SCustom "name") xs nil

  pred instantiate_typ_args i: term, i: list term, o: term.
  instantiate_typ_args (prod Nme {{ Set }} FT) [Arg|Args] Out :-
   !, instantiate_typ_args (FT Arg) Args Out.
  instantiate_typ_args (prod Nme {{ Type }} FT) [Arg|Args] Out :- 
    !, instantiate_typ_args (FT Arg) Args Out.
  instantiate_typ_args T _ T.

  pred uses_fun i:term, o: term, o: term.
  uses_fun (app [{{ SCustom }}|_]) _ _ :- !, fail.
  uses_fun (app [F|Args]) F Typ :-
    coq.typecheck F CoqTyp ok, 
    instantiate_typ_args CoqTyp Args Typ.
  uses_fun (app [_|Args]) F Typ :- 
    std.exists Args (t \ uses_fun t F Typ).

  % pred is_ind_typ o: term.

  % sorts: <A>, list <A>

  % funs: 
    % app : list <A> -> list <A> -> list <A>

  % rels: (none)


  % pred uses_typ i: term, o: term.
  % uses_typ (app [F|_])

  % eq: forall (A: Type) (a a': A), Prop

  % TODO: 
  % If we derive uses_fun Term Fun FunTy, 
  % We can call sort->smt on FunTy to get an SMT type for reflection
    % uses_fun Goal Fun FunTy, 
    % sort->smt FunTy SMTTy.

  pred smt_typ i: term, i: term, o: term.
  smt_typ Goal Ty Out :- 
    uses_fun Goal _ Ty,
    coq.say "Trying to convert to SMT type:" Ty,
    sort->smt Ty Out,
    coq.say "sort->smt output is" Out.

  % (goal Ctx2 REv2 Ty2 Ev2 _)
  solve (goal _ _ Ty _ _ as G) GL :- 
    coq.say "Ty is:" Ty,
    replace_abs_sorts Ty Ty',
    Ty' = (prod _ _ F), 
    Ty'' = (F {{ 0 }}),
    smt_typ Ty'' Fun FunTy,
    coq.say "Output fun is " Fun,
    coq.say "with type " FunTy.
}}.
Elpi Typecheck.

Ltac mirrorsolve' := admit.

Lemma app'_nil_r: 
  forall {A} (xs: list A), app' xs [] = xs.
Proof.
  elpi mirrorsolve. (* for sorts, we expect A, list A *)
  (* ideally the following proof: *)
  induction xs; mirrorsolve'.
Admitted.
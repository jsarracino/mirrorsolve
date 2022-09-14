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

  Inductive List_A := 
  | nil_A 
  | cons_A : A -> List_A -> List_A.

  Infix "::" := cons_A.
  Notation "[]" := nil_A.

  (* We will make use of a hint database to reflect recursive coq functions into SMT logic.
     For now, don't worry about it, but it's handy to use Equations for recursion to make use of the generated equations.
   *)

  Equations app (l: List_A) (r: List_A) : List_A := {
    app [] r := r;
    app (x :: l') r := x :: app l' r;
  }.

  Check app_equation_1. (* forall r : list A, app [] r = r *)
  Check app_equation_2. (* forall (x : A) (l' r : list A), app (x :: l') r = x :: app l' r *)
  
  Equations rev (xs: List_A) : List_A := {
    rev [] := [];
    rev (x :: l') := app (rev l') (x :: []);
  }.

  Equations tail_rev (xs: List_A) (acc: List_A) : List_A := {
    tail_rev [] acc := acc;
    tail_rev (x :: xs') acc := tail_rev xs' (x :: acc);
  }.

  Equations In (x: A) (l: List_A) : Prop := {
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
    forall (x x' : A) (l' : List_A),
      In x (x' :: l') <-> (x = x' \/ In x l').
  Proof.
    intros.
    autorewrite with In.
    intuition eauto.
  Qed.

  (* For simplicity we use Z instead of nat or N, because Z translates directly to SMT. 
     We could also use nat or N and use the N2Z functor to convert goals from nat/N to Z. 
  *)
  Equations len (xs: List_A) : Z := {
    len [] := 0;
    len (_ :: xs) := len xs + 1;
  }.

  Inductive NoDup : List_A -> Prop :=
  | NoDup_nil : NoDup []
  | NoDup_cons : forall x l, 
    ~ In x l -> 
    NoDup l -> 
    NoDup (x::l).

  Lemma NoDup_equation_1 : 
    NoDup [] <-> True.
  Proof.
    intuition eauto || econstructor.
  Qed.

  Lemma NoDup_equation_2 : 
    forall x l, 
      NoDup (x :: l) <-> (
      ~ In x l  /\  NoDup l 
    ).
  Proof.
    intuition eauto.
    - inversion H; subst.
      contradiction.
    - inversion H; subst.
      trivial.
    - econstructor; eauto.
  Qed.

  (* Next we set up a first-order logic for lists, app, rev, tail_rev, In, and len.
   *)

  Declare ML Module "mirrorsolve".

  From MetaCoq.Template Require Import All Loader.
  Import MCMonadNotation.
  Require Import MirrorSolve.Config.
  Open Scope bs.

  Notation pack x := (existT _ _ x).

  Universe foo.
  MetaCoq Quote Definition typ_term := Type@{foo}.

  MetaCoq Run (
    xs <- add_funs typ_term [
        pack ListFuncs.rev
      ; pack ListFuncs.app
      ; pack ListFuncs.List_A
      ; pack ListFuncs.tail_rev
      ; pack ListFuncs.len
      ; pack Z.add
    ] [ 
        pack ListFuncs.In 
      ; pack ListFuncs.NoDup
    ];;
    xs' <- tmQuote xs ;;
    tmMkDefinition "trans_tbl" xs'
  ).
    
  MetaCoq Run (
    gen_sig typ_term sorts fol_funs fol_rels
  ).

  (* Next we give a semantics to the function and relation symbols, in terms of
     the original functions and relation. *)

  (* We used to have the following handwritten interpretation function here: *)
  (*
  Equations interp_fun args ret (f: fol_funs args ret) (hargs : HList.t interp_sorts args) : interp_sorts ret := {
    interp_fun _ _ nil_A_f _ := [];
    interp_fun _ _ cons_A_f (x ::: y ::: hnil) := x :: y;
    interp_fun _ _ app_f (l ::: r ::: hnil):= app l r;
    interp_fun _ _ rev_f (x ::: hnil) := ListFuncs.rev x;
    interp_fun _ _ tail_rev_f (x ::: l ::: hnil) := tail_rev x l;
    interp_fun _ _ len_f (x ::: hnil) := len x;
    interp_fun _ _ add_f (l ::: r ::: hnil) := (l + r)%Z;
    interp_fun _ _ (z_const_f z) hnil := z;
  }.
  *)

  (* Let's try and generate this from what we know. *)

  Require Import MirrorSolve.Reflection.Tactics.

  (* Here are some helper functions; had to crib these from Tactics.v because
     the context there requires a model, and we do not have that yet here. *)

  Fixpoint my_denote_func_type
    (args: list sorts)
    (ret: sorts)
  :
    Type
  := 
    match args with 
    | nil => interp_sorts ret
    | (t :: ts)%list => (interp_sorts t -> (my_denote_func_type ts ret))%type
    end
  .
  
  (* Version of apply_denote_func that works with hlists because that is how
     arguments are supplied when interpreting functions. *)
  Equations my_apply_denote_func
    {arg_tys: list sorts}
    (ret_ty: sorts)
    (args: HList.t interp_sorts arg_tys)
    (f: my_denote_func_type arg_tys ret_ty)
  :
    interp_sorts ret_ty
  := {
    @my_apply_denote_func nil _ _ v => v;
    @my_apply_denote_func (t :: ts) _ (arg ::: args) f =>
      my_apply_denote_func ret_ty args (f arg);
  }.

  (* Helper functions to make the types below check out. I'm sure there is a
     way to get rid of these, but can't find any right now. *)
  Definition fol_fun_args {args ret} (f: fol_funs args ret) : list sorts := args.
  Definition fol_fun_ret {args ret} (f: fol_funs args ret) : sorts := ret.

  (* Here is the association between symbols and functions that is encoded
     in trans_tbl, written out as a function. *)
  Definition denote_func
    {arg_tys: list sorts}
    {ret_ty: sorts}
    (f: fol_funs arg_tys ret_ty)
  :
    my_denote_func_type (fol_fun_args f) (fol_fun_ret f)
  :=
    match f with
    | rev_f => ListFuncs.rev
    | app_f => app
    | nil_A_f => nil_A
    | cons_A_f => cons_A
    | tail_rev_f => tail_rev
    | len_f => len
    | add_f => Z.add
    | z_const_f z => z
    end
  .

  (* Given a function as above, we can generate an interpretation function
     of the right type. *)
  Definition interp_fun
    (arg_tys: list sorts)
    (ret_ty: sorts)
    (f: fol_funs arg_tys ret_ty)
    (hargs : HList.t interp_sorts arg_tys)
  :
    interp_sorts ret_ty
  :=
    my_apply_denote_func ret_ty hargs (denote_func f)
  .

  (* Of course, the objective is to generate even denote_func; we can do this
     as follows. *)

  Definition gen_binder (n: string) := {|
    binder_name := nNamed n;
    binder_relevance := Relevant
  |}.

  Definition gen_denote_func_cases : list (branch term) :=
    List.map (fun '(f, _) => {| bcontext := nil; bbody := f |})
             trans_tbl.(mp_funs)
    ++
    (* This final clause is not part of the translation table, so we add
       it manually. There's probably a better way! *)
    [{| bcontext := [gen_binder "z"]; bbody := tRel 0 |}]%list
  .

  Definition gen_denote_func :=
    q_list_sorts <- tmQuote (list sorts) ;;
    q_sorts <- tmQuote sorts ;;
    q_fol_funs <- tmQuote fol_funs ;;
    fol_funs_ref <- match q_fol_funs with
                    | tInd r _ => tmReturn r
                    | _ => tmFail "fol_funs_ref"
                    end ;;
    q_my_denote_func_type <- tmQuote my_denote_func_type ;;
    q_fol_fun_args <- tmQuote (@fol_fun_args) ;;
    q_fol_fun_ret <- tmQuote (@fol_fun_ret) ;;
    tmMkDefinition "denote_func'"
    (tLambda
      (gen_binder "arg_tys")
      q_list_sorts
      (tLambda
        (gen_binder "ret_ty")
        q_sorts
        (tLambda
          (gen_binder "f")
          (tApp q_fol_funs [tRel 1; tRel 0])
          (tCase
            {|
              ci_ind := fol_funs_ref;
              ci_npar := 0;
              ci_relevance := Relevant
            |}
            {|
              puinst := nil;
              pparams := nil;
              pcontext := [gen_binder "s"; gen_binder "s"; gen_binder "l"];
              preturn :=
                tApp
                  q_my_denote_func_type
                  [tApp q_fol_fun_args [tRel 2; tRel 1; tRel 0];
                   tApp q_fol_fun_ret [tRel 2; tRel 1; tRel 0]]
            |}
            (tRel 0)
            gen_denote_func_cases
          )
        )
      )
    )
  .

  MetaCoq Run gen_denote_func.

  Definition interp_fun'
    (arg_tys: list sorts)
    (ret_ty: sorts)
    (f: fol_funs arg_tys ret_ty)
    (hargs : HList.t interp_sorts arg_tys)
  :
    interp_sorts ret_ty
  :=
    my_apply_denote_func ret_ty hargs (denote_func' _ _ f)
  .
  
  Equations interp_rel args (r: fol_rels args) (hargs : HList.t interp_sorts args) : Prop := {
    interp_rel _ In_r (x ::: l ::: hnil)  := In x l ;
    interp_rel _ NoDup_r (x ::: hnil) := NoDup x;
  }.

  (* We can wrap these definitions together with the previous signature to get a first-order logic *model* for mirrorsolve! *)

  Definition fm_model := Build_model sig interp_sorts interp_fun' interp_rel.

  (* Next we configure the reflection logic for mirrorsolve. 
    So we're going to connect the first-order logic syntax and semantics with Coq's AST in MetaCoq. 
  *)

  Require Import MirrorSolve.Reflection.Tactics.
  
  (* Not sure why but these need to be in separate blocks *)
  MetaCoq Run (
    add_const_wf_instances sig fm_model trans_tbl
  ).
  MetaCoq Run (
    add_matches sig fm_model trans_tbl
  ).
  MetaCoq Run (
    ctx <- build_printing_ctx sig sort_prop trans_tbl [(pack Z.add, "+"%string)];; 
    ctx' <- tmEval all ctx ;;
    rhs <- tmQuote ctx' ;; 
    tmMkDefinition "fol_theory" rhs
  ).

  Require Import MirrorSolve.Reflection.Tactics.

  Transparent denote_tm.
  Require Import MirrorSolve.Axioms.

  Ltac check_goal_unsat := 
    match goal with 
    | |- ?G => check_unsat_neg_func fol_theory G; eapply UnsoundAxioms.interp_true
    end.

  Create HintDb list_eqns.

  Hint Resolve app_equation_1 : list_eqns.
  Hint Resolve app_equation_2 : list_eqns.
  Hint Resolve rev_equation_1 : list_eqns.
  Hint Resolve rev_equation_2 : list_eqns.
  Hint Resolve tail_rev_equation_1 : list_eqns.
  Hint Resolve tail_rev_equation_2 : list_eqns.
  Hint Resolve In_equation_1' : list_eqns.
  Hint Resolve In_equation_2' : list_eqns.
  Hint Resolve len_equation_1 : list_eqns.
  Hint Resolve len_equation_2 : list_eqns.
  Hint Resolve NoDup_equation_1 : list_eqns.
  Hint Resolve NoDup_equation_2 : list_eqns.

  Ltac prep_proof := 
    hints_foreach (fun x => pose proof x) "list_eqns";
    Utils.revert_all;
    unfold "<->" in *.

  Scheme Equality for sorts.

  Ltac quote_reflect_list := quote_reflect sig fm_model sorts_eq_dec match_tacs match_sorts.
  Ltac quote_extract_list := quote_extract sig fm_model sorts_eq_dec match_tacs match_sorts.

  Ltac mirrorsolve :=
    prep_proof;
    quote_reflect_list;
    check_goal_unsat.

  Lemma app_app_one : 
    forall (a: A) (l r : List_A), 
      app (ListFuncs.app l (a::[])) r = app l (a :: r).
  Proof.
    induction l; mirrorsolve.
  Qed.


  Hint Immediate app_app_one : list_eqns.

  Lemma app_assoc : 
    forall (x y z: List_A),
      app (app x y) z = app x (app y z).
  Proof.
    induction x; mirrorsolve.
  Qed.

  Hint Immediate app_assoc : list_eqns.

  Lemma app_nil_r : 
    forall l, app l [] = l.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate app_nil_r : list_eqns.

  Lemma rev_app : 
    forall (l r : List_A), 
      ListFuncs.rev (app l r) = app (ListFuncs.rev r) (ListFuncs.rev l).
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate rev_app : list_eqns.

  Lemma rev_rev : 
    forall (l : List_A), 
      ListFuncs.rev (ListFuncs.rev l) = l.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate rev_rev : list_eqns.

  Lemma tail_rev_spec : 
    forall (l acc : List_A), 
      tail_rev l acc = ListFuncs.app (ListFuncs.rev l) acc.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate tail_rev_spec : list_eqns.

  Lemma tail_rev_sound : 
    forall (l : List_A), 
      ListFuncs.rev l = tail_rev l [].
  Proof.
    idtac "tail_rev_sound".
    induction l; mirrorsolve.
  Qed.

  Hint Immediate tail_rev_sound : list_eqns.

  Lemma app_len : 
    forall (l r : List_A), 
      len (app l r) = (len l + len r)%Z.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate app_len : list_eqns.

  Lemma rev_len :
    forall (l: List_A), 
      len l = len (ListFuncs.rev l).
  Proof.
    induction l; mirrorsolve.
  Qed.
  
  Hint Immediate rev_len : list_eqns.

  Lemma app_In : 
    forall x l r,
      In x (app l r) <-> In x l \/ In x r.
  Proof.
    idtac "app_In".
    induction l; mirrorsolve.
  Qed.

  Hint Immediate app_In : list_eqns.

  Lemma in_rev : 
    forall x l,
      In x l <-> In x (ListFuncs.rev l).
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate in_rev : list_eqns.

  Lemma NoDup_remove :
    forall l l' a, 
    NoDup (app l (a::l')) -> 
    NoDup (app l l') /\ ~In a (app l l').
  Proof.
    idtac "NoDup_remove".
    induction l; mirrorsolve.
  Qed.

  Hint Immediate NoDup_remove : list_eqns.

  Lemma NoDup_remove_1 : 
    forall l l' a,  
      NoDup (app l (a::l')) -> NoDup (app l l').
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate NoDup_remove_1 : list_eqns.

  Lemma NoDup_remove_2 : 
    forall l l' a, 
      NoDup (app l (a::l')) -> 
      ~In a (app l l').
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate NoDup_remove_2 : list_eqns.

  Theorem NoDup_cons_iff :
    forall a l, 
      NoDup (a::l) <-> 
      ~ In a l /\ NoDup l.
  Proof.
    induction l; mirrorsolve.
  Qed.

  Hint Immediate NoDup_cons_iff : list_eqns.

  Lemma NoDup_rev :
    forall l,
      NoDup l -> NoDup (rev l).
  Proof.
    induction l; mirrorsolve.
  Qed.
  

End ListFuncs.
  

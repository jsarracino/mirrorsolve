Require Import MetaCoq.Template.All.
Require Import Coq.Lists.List.
Require Import Coq.Program.Wf.
Require Import Coq.micromega.Lia.
Import String.

Import MCMonadNotation.
Import ListNotations.
Open Scope bs.

Require Import MirrorSolve.Reflection.Meta.

Definition tmDebug {A: Type} (thing: A) : TemplateMonad unit :=
  tmEval all thing >>= tmPrint
.

Definition print_body {A: Type} (f: A) :=
  func_quoted <- tmQuote f ;;
  match func_quoted with
  | tConst kername _ =>
    tmQuoteConstant kername true >>= tmPrint
  | _ =>
    tmFail "Failed to look up body"
  end
.

Require Coq.Strings.BinaryString.
Check Coq.Strings.BinaryString.of_nat.

Eval compute in Coq.Strings.BinaryString.of_nat 5.

Definition n_to_str n :=
  String.of_string (Coq.Strings.BinaryString.of_nat n).

Definition make_binder (n: nat) :=
  {| binder_name := nNamed ("x_" ++ n_to_str n); binder_relevance := Relevant |}
.

Definition subst_recursive_args (rec: term) (args: context) :=
  map (fun arg => subst1 arg.(decl_type) 0 rec) args.

Fixpoint inspect_ctor_args
  (ind_term: term)
  (index: nat)
:=
  match ind_term with
  | tInd ind _ =>
    inductive_definition <- tmQuoteInductive ind.(inductive_mind) ;;
    match inductive_definition.(ind_bodies) with
    | first_body :: nil =>
      match nth_error first_body.(ind_ctors) index with
      | Some inductive_ctor =>
        tmReturn (List.length inductive_ctor.(cstr_args), 0)
      | None =>
        tmFail "Inductive constructor out of range"
      end
    | _ =>
      tmFail "Inductive has more than one body."
    end
  | tApp ind_term inst_args =>
    mlet '(arg_count, inst_arg_count) <- inspect_ctor_args ind_term index ;;
    tmReturn (arg_count, inst_arg_count + #|inst_args|)%list
  | _ =>
    tmDebug ind_term ;;
    tmFail "Term is not an inductive."
  end
.

Fixpoint wrap_type (count: nat) (body: term) :=
  match count with
  | 0 => body
  | S count =>
    tProd (make_binder count) hole (wrap_type count body)
  end
.

Fixpoint wrap_body (count: nat) (body: term) :=
  match count with
  | 0 => body
  | S count =>
    tLambda (make_binder count) hole (wrap_body count body)
  end
.

Fixpoint dummy_args (count: nat) (offset: nat) :=
  match count with
  | 0 => nil
  | S count => List.app (dummy_args count (S offset)) [tRel offset]
  end
.

MetaCoq Quote Definition eq_quoted := @eq.
MetaCoq Quote Definition eq_refl_quoted := @eq_refl.

MetaCoq Quote Definition iff_quoted := @iff.
MetaCoq Quote Definition iff_refl_quoted := @iff_refl.

(* Custom version of MetaCoq's subst function. Theirs assumes that bound terms
   within the arguments will need to be shifted within the produced term, but
   in our case we do not want this to happen.

   Bear in mind that this may be unsound in general because of dependent
   types --- may the CIC gods have mercy on our souls. *)
Fixpoint subst_nolift (s : list term) (k : nat) (u : term) : term :=
  match u with
  | tRel n =>
      if PeanoNat.Nat.leb k n
      then
       match nth_error s (n - k) with
       | Some b => b
       | None => tRel (n - #|s|)
       end
      else tRel n
  | tEvar ev args => tEvar ev (map (subst s k) args)
  | tCast c kind ty => tCast (subst s k c) kind (subst s k ty)
  | tProd na A B => tProd na (subst s k A) (subst s (S k) B)
  | tLambda na T M => tLambda na (subst s k T) (subst s (S k) M)
  | tLetIn na b ty b' =>
      tLetIn na (subst s k b) (subst s k ty) (subst s (S k) b')
  | tApp u0 v => mkApps (subst s k u0) (map (subst s k) v)
  | tCase ind p c brs =>
      let k' := #|pcontext p| + k in
      let p' := map_predicate id (subst s k) (subst s k') p in
      let brs' := map_branches_k (subst s) k brs in
      tCase ind p' (subst s k c) brs'
  | tProj p c => tProj p (subst s k c)
  | tFix mfix idx =>
      let k' := #|mfix| + k in
      let mfix' := map (map_def (subst s k) (subst s k')) mfix in
      tFix mfix' idx
  | tCoFix mfix idx =>
      let k' := #|mfix| + k in
      let mfix' := map (map_def (subst s k) (subst s k')) mfix in
      tCoFix mfix' idx
  | _ => u
  end.

Definition infer_equation
  (arg_type_quoted: term)
  (ret_type_quoted: term)
  (func_ref: kername * Instance.t)
  (info: case_info)
  (body: term)
  (depth: nat)
  (offset: nat)
  (index: nat)
:=
  mlet (arg_count, inst_arg_count) <- inspect_ctor_args arg_type_quoted index ;;
  let (func_kername, func_inst) := func_ref in
  let (func_path, func_name) := func_kername in
  let construct := tApp (tConstruct info.(ci_ind) index [])
                        (repeat hole inst_arg_count
                         ++ dummy_args arg_count 0)%list in
  let args_pre := dummy_args (depth-1-offset) (offset+arg_count) in
  let args_post := dummy_args offset arg_count in
  let args := (args_pre ++ [construct] ++ args_post)%list in
  let claim_lhs := tApp (tConst func_kername func_inst) args in
  let claim_rhs := subst_nolift [construct] (offset+arg_count) body in
  let (claim_prefix, proof_prefix) :=
    match ret_type_quoted with
    | tSort Universe.lProp =>
      (iff_quoted, iff_refl_quoted)
    | _ =>
      (tApp eq_quoted [hole], tApp eq_refl_quoted [hole])
    end in
  let claim_eq := tApp claim_prefix [claim_lhs; claim_rhs] in
  let claim_quoted := wrap_type (arg_count+depth-1) claim_eq in
  claim <- tmUnquoteTyped Type claim_quoted ;;
  let proof_quoted :=
    wrap_body (arg_count+depth-1) (tApp proof_prefix [claim_rhs]) in
  proof <- tmUnquoteTyped claim proof_quoted ;;
  let eqn_base := func_name ++ "_equation_" ++ string_of_nat (index+1) in
  eqn_name <- tmFreshName eqn_base ;;
  tmDefinitionRed eqn_name (Some (unfold (Common_kn "my_projT1"))) proof ;;
  tmReturn tt
.

Fixpoint infer_equations_walk_cases
  (arg_type_quoted: term)
  (ret_type_quoted: term)
  (func_ref: kername * Instance.t)
  (info: case_info)
  (bodies: list (branch term))
  (depth: nat)
  (offset: nat)
  (index: nat)
:
  TemplateMonad unit
:=
  match bodies with
  | nil => tmReturn tt
  | body :: bodies =>
    infer_equation arg_type_quoted ret_type_quoted func_ref info body.(bbody) depth offset index ;;
    infer_equations_walk_cases arg_type_quoted ret_type_quoted func_ref info bodies depth offset (S index)
  end
.

Fixpoint term_lambda_depth (u : term) : nat :=
  match u with
  | tEvar _ args =>
    list_max (map term_lambda_depth args)
  | tCast c _ ty =>
    max (term_lambda_depth c) (term_lambda_depth ty)
  | tProd _ A B =>
    max (term_lambda_depth A) (term_lambda_depth B)
  | tLambda _ T M =>
    max (term_lambda_depth T) (S (term_lambda_depth M))
  | tLetIn _ b ty b' =>
    list_max [
      term_lambda_depth b;
      term_lambda_depth ty;
      term_lambda_depth b'
    ]
  | tApp u0 v =>
    list_max (map term_lambda_depth (u0 :: v))
  | tCase _ p c brs =>
    list_max (map term_lambda_depth p.(pparams)
             ++ [term_lambda_depth p.(preturn)]
             ++ [term_lambda_depth c]
             ++ map (term_lambda_depth ∘ bbody) brs)
  | tProj _ c =>
    term_lambda_depth c
  | tFix mfix _
  | tCoFix mfix _ =>
    list_max (map (term_lambda_depth ∘ dtype) mfix
              ++ map (S ∘ term_lambda_depth ∘ dbody) mfix)
  | _ => 0
  end
.

Lemma term_lambda_depth_lift (t: term) (n m: nat):
  term_lambda_depth (lift n m t) = term_lambda_depth t
.
Proof.
  revert n m; induction t using term_ind'; intros; simpl; try congruence.
  - rewrite Forall_forall in H.
    rewrite map_map.
    now erewrite map_ext_in.
  - rewrite Forall_forall in H.
    f_equal; auto.
    rewrite map_map.
    now erewrite map_ext_in.
  - rewrite Forall_forall in H, H0.
    f_equal; f_equal; [| f_equal; [| f_equal]].
    + now erewrite map_map, map_ext_in.
    + now rewrite IHt.
    + now rewrite IHt0.
    + erewrite map_map, map_ext_in; intuition.
  - rewrite Forall_forall in H, H0.
    f_equal; f_equal; erewrite map_map, map_ext_in; intuition.
  - rewrite Forall_forall in H, H0.
    f_equal; f_equal; erewrite map_map, map_ext_in; intuition.
Qed.

Lemma term_lambda_depth_mkApps (t: term) (args: list term):
  term_lambda_depth (mkApps t args) = term_lambda_depth (tApp t args)
.
Proof.
  destruct args; simpl.
  - lia.
  - destruct t; simpl; try lia.
    rewrite map_app, list_max_app.
    simpl; lia.
Qed.

Lemma list_max_In (l: list nat) (n: nat):
  In n l ->
  n <= list_max l
.
Proof.
  induction l; intros; destruct H; simpl.
  - lia.
  - etransitivity; swap 1 2.
    + apply PeanoNat.Nat.le_max_r.
    + intuition.
Qed.

Lemma list_max_add_distr_l (l: list nat) (n: nat):
  l <> nil ->
  n + list_max l = list_max (map (Nat.add n) l)
.
Proof.
  induction l; simpl; intros.
  - contradiction.
  - destruct l.
    + simpl; lia.
    + rewrite PeanoNat.Nat.max_comm.
      rewrite <- IHl.
      * lia.
      * intro.
        discriminate.
Qed.

Lemma term_lambda_depth_subst1 (t u: term) (n: nat):
  term_lambda_depth (subst [t] n u) <= term_lambda_depth t + term_lambda_depth u
.
Proof.
  revert n; induction u using term_ind'; intros; simpl; try lia.
  - destruct (PeanoNat.Nat.leb _ _).
    + destruct (n - n0); simpl.
      * now rewrite term_lambda_depth_lift.
      * rewrite nth_error_nil; simpl; lia.
    + now simpl.
  - apply list_max_le.
    rewrite Forall_forall; intros.
    rewrite Forall_forall in H.
    rewrite map_map in H0.
    apply in_map_iff in H0.
    destruct H0 as [t' [? ?]]; subst.
    etransitivity.
    + now apply H.
    + apply PeanoNat.Nat.add_le_mono_l.
      apply list_max_In.
      apply in_map_iff.
      now exists t'.
  - specialize (IHu1 n).
    specialize (IHu2 n).
    lia.
  - specialize (IHu1 n).
    specialize (IHu2 (S n)).
    lia.
  - specialize (IHu1 n).
    specialize (IHu2 (S n)).
    lia.
  - specialize (IHu1 n).
    specialize (IHu2 n).
    specialize (IHu3 (S n)).
    lia.
  - rewrite term_lambda_depth_mkApps; simpl.
    rewrite Forall_forall in H.
    rewrite <- Max.plus_max_distr_l.
    apply Max.max_lub.
    + specialize (IHu n); lia.
    + apply list_max_le.
      apply Forall_forall; intros.
      rewrite map_map in H0.
      apply in_map_iff in H0.
      destruct H0 as [t' [? ?]]; subst.
      rewrite <- PeanoNat.Nat.le_max_r.
      rewrite list_max_add_distr_l.
      * rewrite map_map.
        rewrite H by auto.
        apply list_max_In.
        apply in_map_iff.
        eexists; auto.
      * intro.
        apply map_eq_nil in H0; now subst.
  - rewrite list_max_add_distr_l.
    + repeat rewrite map_app.
      repeat rewrite map_map.
      rewrite Forall_forall in H, H0.
      apply list_max_le, Forall_forall; intros.
      apply in_app_iff in H1; simpl in H1.
      repeat rewrite list_max_app; simpl.
      destruct H1 as [? | [? | [? | ?]]]; subst.
      * apply in_map_iff in H1.
        destruct H1 as [t' [? ?]]; subst.
        rewrite <- PeanoNat.Nat.le_max_l.
        etransitivity; swap 1 2.
        apply list_max_In.
        apply in_map_iff.
        now exists t'.
        now apply H.
      * specialize (IHu (#|pcontext type_info| + n)); lia.
      * specialize (IHu0 n); lia.
      * repeat rewrite <- PeanoNat.Nat.le_max_r.
        rewrite map_map.
        apply in_map_iff in H1.
        destruct H1 as [? [? ?]]; subst.
        etransitivity; [now apply H0|].
        apply list_max_In.
        apply in_map_iff.
        now eexists.
    + intro.
      apply (f_equal (@List.length nat)) in H1.
      rewrite app_length in H1; simpl in H1.
      lia.
  - apply IHu.
  - apply list_max_le, Forall_forall; intros.
    rewrite in_app_iff in H1.
    rewrite list_max_add_distr_l.
    + repeat rewrite in_map_iff in H1.
      destruct H1.
      * destruct H1 as [? [? ?]]; subst.
        apply in_map_iff in H2.
        destruct H2 as [? [? ?]]; subst.
        rewrite <- map_dtype.
        rewrite map_app, list_max_app.
        rewrite Forall_forall in H.
        rewrite H by auto.
        rewrite <- PeanoNat.Nat.le_max_l.
        rewrite map_map.
        apply list_max_In.
        apply in_map_iff.
        now eexists.
      * destruct H1 as [? [? ?]]; subst.
        apply in_map_iff in H2.
        destruct H2 as [? [? ?]]; subst.
        rewrite <- map_dbody.
        rewrite map_app, list_max_app.
        rewrite Forall_forall in H0.
        rewrite <- PeanoNat.Nat.le_max_r.
        etransitivity; swap 1 2.
        rewrite map_map.
        apply list_max_In.
        apply in_map_iff.
        now eexists.
        specialize (H0 _ H2 (#|mfix| + n)).
        lia.
    + intro.
      apply (f_equal (@List.length nat)) in H2.
      rewrite app_length in H2; simpl in H2.
      repeat rewrite map_length in H2.
      apply Plus.plus_is_O in H2.
      destruct H2 as [? _].
      apply length_zero_iff_nil in H2.
      destruct H1.
      * rewrite map_map in H1.
        rewrite in_map_iff in H1.
        destruct H1 as [? [? ?]].
        now subst.
      * rewrite map_map in H1.
        rewrite in_map_iff in H1.
        destruct H1 as [? [? ?]].
        now subst.
  - apply list_max_le, Forall_forall; intros.
    rewrite in_app_iff in H1.
    rewrite list_max_add_distr_l.
    + repeat rewrite in_map_iff in H1.
      destruct H1.
      * destruct H1 as [? [? ?]]; subst.
        apply in_map_iff in H2.
        destruct H2 as [? [? ?]]; subst.
        rewrite <- map_dtype.
        rewrite map_app, list_max_app.
        rewrite Forall_forall in H.
        rewrite H by auto.
        rewrite <- PeanoNat.Nat.le_max_l.
        rewrite map_map.
        apply list_max_In.
        apply in_map_iff.
        now eexists.
      * destruct H1 as [? [? ?]]; subst.
        apply in_map_iff in H2.
        destruct H2 as [? [? ?]]; subst.
        rewrite <- map_dbody.
        rewrite map_app, list_max_app.
        rewrite Forall_forall in H0.
        rewrite <- PeanoNat.Nat.le_max_r.
        etransitivity; swap 1 2.
        rewrite map_map.
        apply list_max_In.
        apply in_map_iff.
        now eexists.
        specialize (H0 _ H2 (#|mfix| + n)).
        lia.
    + intro.
      apply (f_equal (@List.length nat)) in H2.
      rewrite app_length in H2; simpl in H2.
      repeat rewrite map_length in H2.
      apply Plus.plus_is_O in H2.
      destruct H2 as [? _].
      apply length_zero_iff_nil in H2.
      destruct H1.
      * rewrite map_map in H1.
        rewrite in_map_iff in H1.
        destruct H1 as [? [? ?]].
        now subst.
      * rewrite map_map in H1.
        rewrite in_map_iff in H1.
        destruct H1 as [? [? ?]].
        now subst.
Qed.

Polymorphic Program Fixpoint infer_equations_inner
  (body: term)
  (func_ref: kername * Instance.t)
  (context: list term)
  {measure (term_lambda_depth body)}
:
  TemplateMonad unit
:=
  match body with
  | tLambda _ arg_type_quoted body =>
    infer_equations_inner body func_ref (arg_type_quoted :: context)
  | tCase info pred (tRel offset) bodies =>
    match nth_error context offset with
    | Some arg_type_quoted =>
      infer_equations_walk_cases arg_type_quoted pred.(preturn) func_ref info bodies (List.length context) offset 0
    | None =>
      tmFail "Term contains match on something that is not an argument."
    end
  | tFix (first_fixpoint :: nil) 0 =>
    let rec_call := tApp (uncurry tConst func_ref) (dummy_args #|context| 0) in
    let body := subst10 rec_call first_fixpoint.(dbody) in
    infer_equations_inner body func_ref context
  | _ =>
    tmFail "Symbol body is not a function with a match inside."
  end
.
Next Obligation.
  simpl; lia.
Qed.
Next Obligation.
  simpl.
  eapply PeanoNat.Nat.le_lt_trans.
  - apply term_lambda_depth_subst1.
  - simpl.
    eapply PeanoNat.Nat.le_lt_trans.
    + apply PeanoNat.Nat.add_le_mono_r.
      instantiate (1 := 0).
      generalize 0 at 1; induction context0; simpl; intros.
      * lia.
      * rewrite map_app; simpl.
        rewrite list_max_app; simpl.
        rewrite PeanoNat.Nat.max_0_r.
        apply IHcontext0.
    + lia.
Qed.
Solve Obligations with (repeat split; intros; intro; discriminate).

Definition infer_equations {A: Type} (func: A) :=
  func_quoted <- tmQuote func ;;
  match func_quoted with
  | tConst func_path func_inst =>
    def <- tmQuoteConstant func_path true ;;
    match def.(cst_body) with
    | Some body =>
      infer_equations_inner body (func_path, func_inst) nil
    | None =>
      tmFail "Function does not seem to have a body."
    end
  | _ => tmFail "Symbol is not a constant."
  end
.

Section Tests.
  Definition decr (n: nat) : nat :=
    match n with
    | 0 => 0
    | S n => n
    end
  .
  MetaCoq Run (infer_equations decr).
  Check decr_equation_1.
  Check decr_equation_2.

  Definition decr_strange (n: nat) : nat :=
    match n with
    | 0 => 0
    | S m => n
    end
  .

  MetaCoq Run (infer_equations decr_strange).
  Check decr_strange_equation_1.
  Check decr_strange_equation_2.

  Definition decr_multi_arg (n m: nat) :=
    match n with
    | 0 => m
    | S n => n
    end.

  MetaCoq Run (infer_equations decr_multi_arg).
  Check decr_multi_arg_equation_1.
  Check decr_multi_arg_equation_2.

  Fixpoint decr_rec (n: nat) : nat :=
    match n with
    | 0 => 0
    | S n => decr_rec n
    end
  .

  MetaCoq Run (infer_equations decr_rec).
  Check decr_rec_equation_1.
  Check decr_rec_equation_2.

  Fixpoint decr_rec_multi_arg (n m: nat) : nat :=
    match n with
    | 0 => m
    | S n => decr_rec_multi_arg n m
    end
  .

  MetaCoq Run (infer_equations decr_rec_multi_arg).
  Check decr_rec_multi_arg_equation_1.
  Check decr_rec_multi_arg_equation_2.

  MetaCoq Run (infer_equations Nat.add).
  Check add_equation_1.
  Check add_equation_2.

  MetaCoq Run (infer_equations Nat.mul).
  Check mul_equation_1.
  Check mul_equation_2.

  Fixpoint NoDup_nat (xs: list nat) :=
    match xs with
    | [] => True
    | x' :: xs' =>
      ~ In x' xs' /\ NoDup_nat xs'
    end.
  MetaCoq Run (infer_equations NoDup_nat).
  Check NoDup_nat_equation_1.
  Check NoDup_nat_equation_2.

  MetaCoq Run (infer_equations List.app).
  Check app_equation_1.
  Check app_equation_2.

  MetaCoq Run (infer_equations List.rev).
  Check rev_equation_1.
  Check rev_equation_2.

  MetaCoq Run (infer_equations In).
  Check In_equation_1.
  Check In_equation_2.

  Definition In_A := Eval compute in @In nat.

  MetaCoq Run (infer_equations In_A).
  Check In_A_equation_1.
  (* forall x_0b0 : nat, In_A x_0b0 [] <-> False *)

  Lemma in_In_A : forall x xs, In_A x xs <-> In x xs.
  Proof.
    intros; eapply iff_refl.
  Qed.
End Tests.

(* The term we are trying to generate has a lot of leeway for holes! *)
Definition NoDup_equation_2 :
    forall A x (l: list A),
      @NoDup A (x :: l) -> _
    := (
    fun _ _ =>
      (fun _ y =>
        match y in (NoDup y') return
          match y' with
          | _ :: _ => _
          | _ => _
          end
        with
        | NoDup_nil => I
        | NoDup_cons _ _ p q => conj p q
        end
      )
  ).

Check NoDup_equation_2.

Definition binder_anon :=
  {| binder_name := nAnon;
     binder_relevance := Relevant |}
.

MetaCoq Quote Definition I_quoted := I.

Definition inductive_extract_body (ind: inductive) : TemplateMonad _ :=
  ind_def <- tmQuoteInductive ind.(inductive_mind) ;;
  match ind_def.(ind_bodies) with
  | ind_body :: nil =>
    tmReturn ind_body
  | _ =>
    tmFail "Inductive parameter type has more than one body"
  end
.

Definition infer_equivalences_gen_match_return
  (ind: inductive)
:
  TemplateMonad term
:=
  ind_body <- inductive_extract_body ind ;;
  let generate_case ctor :=
    {| bcontext := repeat binder_anon #|ctor.(cstr_args)|;
       bbody := hole |} in
  tmReturn
    (tCase {| ci_ind := ind;
              ci_npar := 1;
              ci_relevance := Relevant |}
           {| puinst := [];
              pparams := [hole];
              pcontext := [binder_anon];
              preturn := hole |}
           (tRel 1)
           (map generate_case ind_body.(ind_ctors)))
.


MetaCoq Quote Definition conj_quoted := conj.

Fixpoint nest_conjunction (n: nat) :=
    match n with
    | 0 => I_quoted
    | S n => tApp conj_quoted [hole; hole; tRel 0; lift0 1 (nest_conjunction n)]
    end.

Definition infer_equivalences_gen_match_term
  (ind: inductive)
  (term_ret: term)
:
  TemplateMonad term
:=
  ind_body <- inductive_extract_body ind ;;
  let generate_case ctor : TemplateMonad (branch term) :=
    match ctor.(cstr_indices) with
    | tApp (tConstruct _ _ _) indexed_args :: nil =>
      (* TODO: Properly figure out the number of args to skip here. *)
      let arg_count := #|ctor.(cstr_args)|
                       + #|ind_body.(ind_indices)|
                       - #|indexed_args| in
      tmReturn {| bcontext := repeat binder_anon #|ctor.(cstr_args)|;
                  bbody := nest_conjunction arg_count |}
    | _ =>
      tmFail "Failed to retrieve indexed arguments"
    end in
  bodies <- monad_map generate_case ind_body.(ind_ctors) ;;
  let ret := (tCase {| ci_ind := ind;
              ci_npar := 1;
              ci_relevance := Relevant |}
           {| puinst := [];
              pparams := [hole];
              pcontext := [binder_anon; binder_anon];
              preturn := term_ret |}
           (tRel 0)
           bodies) in
  tmReturn ret
.

Fixpoint infer_equivalences_walk_cstrs
  (cstrs: list constructor_body)
  (main_ind: inductive)
  (param_ind: inductive)
  (ctx: context)
  (index: nat)
:
  TemplateMonad unit
:=
  match cstrs with
  | cstr :: cstrs =>
    let full_ctx := app_context ctx cstr.(cstr_args) in
    let full_ctx_fill := subst_context (tInd param_ind [] :: nil) 0 full_ctx in
    let inserted_arg := tApp (tConstruct param_ind index [])
                             (dummy_args #|full_ctx| 0) in
    let main_args := List.app (dummy_args #|ctx| #|cstr.(cstr_args)|)
                              (inserted_arg :: nil) in
    let destructable := tApp (tInd main_ind []) main_args in
    let fix build_quantification ctx :=
      match ctx with
      | nil => tProd binder_anon destructable hole
      | arg :: ctx =>
        tProd binder_anon arg.(decl_type) (build_quantification ctx)
      end in
    let claim := build_quantification (List.rev full_ctx_fill) in
    claim_unquoted <- tmUnquoteTyped Type claim ;;
    match_return <- infer_equivalences_gen_match_return param_ind ;;
    match_term <- infer_equivalences_gen_match_term main_ind match_return ;;
    let fix build_function (n: nat) :=
      match n with
      | 0 => tLambda binder_anon destructable match_term
      | S n => tLambda binder_anon hole (build_function n)
      end in
    let term_whole := build_function #|full_ctx_fill| in
    proof <- tmUnquoteTyped claim_unquoted term_whole ;;
    eqn_name <- tmFreshName "equivalence" ;;
    tmDefinitionRed eqn_name (Some (unfold (Common_kn "my_projT1"))) proof ;;
    infer_equivalences_walk_cstrs cstrs main_ind param_ind ctx (S index)
  | nil =>
    tmReturn tt
  end
.

Fixpoint infer_equivalences_walk_params
  (main_ind: inductive)
  (params: context)
:
  TemplateMonad unit
:=
  match params with
  | nil =>
    tmReturn tt
  | param :: params =>
    match param.(decl_type) with
    | tApp (tInd param_ind _) param_ind_args =>
      param_ind_body <- inductive_extract_body param_ind ;;
      infer_equivalences_walk_cstrs param_ind_body.(ind_ctors)
                                    main_ind param_ind params 0
    | _ =>
      tmReturn tt
    end ;;
    infer_equivalences_walk_params main_ind params
  end
.

Definition infer_equivalences
  {A: Type}
  (ind_ref: A)
:
  TemplateMonad unit
:=
  ind_quoted <- tmQuote ind_ref ;;
  match ind_quoted with
  | tInd ind inst =>
    ind_definition <- tmQuoteInductive ind.(inductive_mind) ;;
    ind_body <- inductive_extract_body ind ;;
    let params := app_context ind_definition.(ind_params)
                              ind_body.(ind_indices) in
    infer_equivalences_walk_params ind params
  | _ => tmFail "Symbol is not an inductive."
  end
.

MetaCoq Run (infer_equivalences NoDup).

Check equivalence.
Check equivalence0.

(* A more contrived version of NoDup to make this more of a challenge. *)

Inductive NoDup' (A : Type) : list A -> Prop :=
| NoDup_nil' : NoDup' _ nil
| NoDup_cons' : forall (x : A) (l : list A),
               ~ In x l -> NoDup' _ l -> NoDup' _ (x :: l)
| NoDup_cons2' : forall (x : A) (l : list A),
                 True -> ~ In x l -> NoDup' _ l -> NoDup' _ (x :: l)
.

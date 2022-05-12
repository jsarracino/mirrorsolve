

Require Import Coq.ZArith.BinInt.
Require Import Coq.Classes.EquivDec.

Require Import Coq.Lists.List.

Section Boogie.

  Inductive Typ := 
  | TInt.

  Scheme Equality for Typ.

  Variable (Var: Typ -> Set).
  Variable (var_eq_dec : forall t, EqDec (Var t) eq).

  Inductive Expr : Typ -> Type := 
  | Plus : Expr TInt -> Expr TInt -> Expr TInt
  | Minus : Expr TInt -> Expr TInt -> Expr TInt
  | ILit : Z -> Expr TInt
  | EVar : forall {t}, Var t -> Expr t.

  Definition Value (t: Typ) := 
    match t with 
    | TInt => Z
    end.

  Definition State := forall t (v: Var t), Value t.

  Definition put {t} (v: Var t) (rhs: Value t) (st: State) : State := 
    fun t' (v': Var t') =>
      match Typ_eq_dec t t' with 
      | left H => 
        if v' == (eq_rect _ _ v _ H) then (eq_rect _ _ rhs _ H) else st _ v'
      | right _ => st _ v'
      end.

  Definition get {t} (v: Var t) (st: State) : Value t := st _ v.

  Fixpoint eval_expr {t} (st: State) (e: Expr t) : Value t :=
    match e in Expr t' return Value t' with 
    | Plus l r => (eval_expr st l + eval_expr st r)%Z
    | Minus l r => (eval_expr st l - eval_expr st r)%Z
    | ILit v => v
    | EVar v => get v st
    end.

  Inductive Command := 
  | Seq: forall (c1 c2 : Command), Command
  | Assign: forall {t} (v: Var t) (rhs: Expr t), Command
  | Assert: forall (test: State -> Prop), Command
  | Assume: forall (test: State -> Prop), Command
  | Havoc: forall {t} (v: Var t), Command
  | Cond: forall (test: State -> Prop) (c_true : Command) (c_false: Command), Command
  | While: forall (test: State -> Prop) (inv: State -> Prop) (measure: State -> nat) (modifies : list {t & Var t}) (body: Command), Command.

  Fixpoint quantify_vars (s: State) (Pred: State -> Prop) (vars: list {t & Var t}) : Prop := 
    match vars with 
    | nil => Pred s
    | existT _ t v :: vars' =>
      forall (rhs: Value t), 
        quantify_vars (put v rhs s) Pred vars'
    end.  

  Definition skip := Assert (fun _ => True).

  Fixpoint unroll_loop (n: nat) (test: State -> Prop) (body: Command) : Command := 
    match n with 
    | 0 => skip
    | S n => Cond test (unroll_loop n test body) skip
    end.

  Inductive semantics : Command -> State -> State -> Prop := 
  | SemSeq : forall c1 c2 s s' s'', 
    semantics c1 s s' -> 
    semantics c2 s' s'' -> 
    semantics (Seq c1 c2) s s''
  | SemAssign : forall t v rhs s s', 
    s' = put v (eval_expr s rhs) s ->
    semantics (@Assign t v rhs) s s'
  | SemAssert : forall (test: State -> Prop) s s', 
    test s -> 
    s = s' -> 
    semantics (Assert test) s s'
  | SemAssume : forall (test: State -> Prop) s s', 
    test s -> 
    s = s' -> 
    semantics (Assume test) s s'
  | SemHavoc : forall t v s s',
    forall (rhs: Value t), 
      s' = put v rhs s -> 
      semantics (@Havoc t v) s s'
  | SemCond : forall (test : State -> Prop) ct cf s s', 
    (test s -> semantics ct s s') -> 
    (~ test s -> semantics cf s s') -> 
    semantics (Cond test ct cf) s s'
  | SemWhileDone : forall (test : State -> Prop) inv measure modifies body s s',
    ~ test s -> 
    s = s' -> 
    semantics (While test inv measure modifies body) s s' 
  | SemWhileIter : forall (test : State -> Prop) inv measure body modifies s s' s'',
    test s -> 
    semantics body s s' -> 
    semantics (While test inv measure modifies body) s' s'' -> 
    semantics (While test inv measure modifies body) s s''. 

  Lemma inv_assign : 
    forall {t v rhs s s'}, 
      semantics (@Assign t v rhs) s s' -> 
      s' = put v (eval_expr s rhs) s.
  Proof.
    intros.
    refine (
      match H with 
      | SemAssign _ _ _ _ _ _ => _ 
      end
    ); trivial.
  Qed.

  Ltac red_env := 
    repeat match goal with
    | H : semantics (Seq _ _) _ _ |- _ => 
      inversion H; subst; clear H
    | H : semantics (Assign _ _) _ _ |- _ => 
      let H' := fresh "H'" in 
      pose proof (H': inv_assign H);
      subst;
      clear H;
      clear H'
    | H : _ /\ _ |- _ => destruct H
    end.


  Fixpoint wp (c: Command) (Pred: State -> Prop) {struct c} : State -> Prop.
  refine (
    match c with 
    | Seq c1 c2 => wp c1 (wp c2 Pred)
    | Assign v rhs => fun s => Pred (put v (eval_expr s rhs) s)
    | Assert test => fun s => test s /\ Pred s
    | Assume test => fun s => (test s -> Pred s)
    | @Havoc t v => fun s => forall (rhs: Value t), Pred (put v rhs s)
    | Cond test ct cf => fun s => (test s /\ wp ct Pred s) \/ (~ test s /\ wp cf Pred s)
    | While test inv measure modifies body => fun s => 
      inv s /\ (
        quantify_vars s (fun s' => 
          (test s' /\ inv s' -> wp body inv s') /\ 
          (~ test s' /\ inv s' -> Pred s')
        ) modifies
      )
    end
  ).
  Defined.

  (* we need inhabitance for the soundness of the Havoc rule,
     to connect the two different versions of Havoc
  *)
  Definition inhabited_Typ (t: Typ) : inhabited (Value t) := 
    match t with 
    | TInt => inhabits 0%Z
    end.

  Lemma wp_spec :
    forall (c: Command) (Pred: State -> Prop) (s s' : State), 
      semantics c s s' -> 
      wp c Pred s -> 
      Pred s'.
  Proof.
  Admitted.
    (* induction c; simpl; intros; try subst; trivial.
    - simpl in *.
      inversion H; subst; clear H.
      pose proof (IHc1 (wp c2 Pred)).
      eapply IHc2; intuition eauto.
    - inversion H; subst; clear H.
      simpl in *.
      intuition eauto.
      subst; trivial.
    - intuition eauto.
      subst.
      trivial.
    - pose proof (inhabited_Typ t).
      destruct H1 as [rhs].
      specialize (H rhs).
      erewrite H.
      eapply H0.
    - intuition eauto.
      * eapply IHc1;
        intuition eauto.
      * eapply IHc2; intuition eauto.
  Qed. *)

  Definition pred_top := fun (s : State) => True.
End Boogie.

Section McCarthy91.

  (* procedure F(n: int) returns (r: int)
  ensures 100 < n ==> r == n - 10;
  ensures n <= 100 ==> r == 91;
  {
    if (100 < n) {
      r := n - 10;
    } else {
      call r := F(n + 11);
      call r := F(r);
    }
  } *)

  Inductive M91Vars : Typ -> Set := | R : M91Vars TInt | N : M91Vars TInt.

  Definition v0_eq_dec : EqDec (M91Vars TInt) eq.
  refine (
    fun l => 
      match l with 
      | R => fun r => 
        match r with 
        | R => left _
        | N => right _ 
        end
      | N => fun r => 
        match r with 
        | R => right _ 
        | N => left _
        end
      end
  ); congruence.
  Defined.

  Definition var_eq_dec (t: Typ) : EqDec (M91Vars t) eq.
  refine (
    fun x y => _
  );
  destruct t; 
  match goal with 
  (* | H : M91Vars TBool |- _ => inversion H
  | H : M91Vars (TMap _ _) |- _ => inversion H *)
  | _ => eapply v0_eq_dec
  end.
  Defined.

  Notation assert := (@Assert M91Vars).
  Notation assume := (@Assume M91Vars).
  Notation seq := (@Seq M91Vars).
  Notation top := (@pred_top M91Vars).

  Notation lit := (@ILit M91Vars).
  Notation var := (@EVar M91Vars). 
  Notation plus := (@Plus M91Vars).
  Notation minus := (@Minus M91Vars).
  Notation havoc := (@Havoc M91Vars).

  Infix ";;" := (seq) (at level 150).
  Notation "x '<-' v" := (@Assign M91Vars _ x v) (at level 98).

  Notation "'If' c 'Then' ct 'Else' cf" := (@Cond M91Vars c ct cf) (at level 99).

  Require Import Coq.micromega.Lia.

  Definition test_1 := 
    assume (fun st => st _ R = st _ N)%Z ;;
    R <- (plus (var R) (lit 1%Z)) ;;
    R <- (plus (var R) (lit 1%Z)).

  Notation semantics := (semantics M91Vars var_eq_dec).

  Ltac red_env := 
    repeat match goal with
    | H : semantics (_ ;; _) _ _ |- _ => 
      inversion H; subst; clear H
    | H : semantics (_ <- _) _ _ |- _ => 
      let H' := fresh "H'" in 
      pose proof (H': inv_assign _ _ H);
      subst;
      clear H;
      clear H'
    | H : _ /\ _ |- _ => destruct H
    end.

  Goal forall st st', 
    semantics test_1 st st' -> 
    (st' _ N = st _ N) /\ (st' _ R = st _ N + 2)%Z.
  Proof.
    intros.
    unfold test_1 in H.
    red_env.
    inversion H1; subst.
    clear H1.
    pose proof (inv_assign _ _ H6).
    pose proof (inv_assign _ _ H5).
    subst.
    split; [trivial|].
    simpl put.

    unfold get, put.
    simpl.
    inversion H0.
    Lia.lia.
  Qed.

  Goal forall (st : State M91Vars), wp M91Vars var_eq_dec test_1 (fun st' => st' _ R = st' _ N + 2 /\ st' _ N = st _ N)%Z st.
  Proof.
    intros.
    simpl wp.
    intuition.
    unfold get, put; simpl.
    Lia.lia.
  Qed.
(* 
  procedure ok2()
{
  var x:int, y:int;
  var a:t1, b:t1, c:t1;

  c := if x > y then a else b;
  assert c == a || c == b;
  assume x > y;
  assert c == a;
} *)

  Definition test_2 := 
    If (fun st => st _ R < st _ N)%Z
    Then (R <- lit 10)%Z
    Else (assert top).

  Definition test_2_post_weak (s: State M91Vars) := 
    (s _ R < s _ N -> s _ R = 10)%Z.
  Definition test_2_post_strong (s: State M91Vars) := 
    s _ R = 10%Z.

  Goal forall st, wp M91Vars var_eq_dec test_2 test_2_post_weak st.
  Proof.
    intros.
    simpl wp.
    unfold put, test_2_post_weak.
    simpl.
    intuition.
    assert (st _ R < st _ N \/ ~ (st _ R < st _ N))%Z by Lia.lia.
    destruct H.
    - left; intuition.
    - right; intuition; exact I.
  Qed.


  Definition mc_post (st: State M91Vars) : Prop := 
    (* ensures 100 < n ==> r == n - 10;
       ensures n <= 100 ==> r == 91 *)
    (((100 < st _ N) -> (st _ R = st _ N - 10)) /\ 
    ((st _ N <= 100) -> (st _ R = 91)))%Z.

  Definition mccarthy := 
    If (fun st => 100 < st _ N)%Z
    Then (R <- minus (var N) (lit 10))%Z
    Else (
      (*  call r := F(n + 11);
          call r := F(r); *)
      havoc R ;; 
      havoc N ;;
      assume mc_post
    ).

  Require Import Coq.ZArith.BinInt.

  Require Import MirrorSolve.FirstOrder.

  Require Import MirrorSolve.Z.
  Require Import MirrorSolve.SMT.

  Require Import MirrorSolve.HLists.
  Require Import Coq.Lists.List.

  Import HListNotations.
  Import ListNotations.

  Require Import Coq.Strings.String.

  Require Import MirrorSolve.Reflection.Core.
  Require Import MirrorSolve.Reflection.FM.

  Require Import Coq.Bool.Bool.

  Require Import MirrorSolve.Reflection.Tactics.

  MetaCoq Quote Definition c_lt := Z.ltb.
  MetaCoq Quote Definition c_le := Z.leb.
  MetaCoq Quote Definition c_minus := Z.sub.

  MetaCoq Quote Definition c_tru := true.
  MetaCoq Quote Definition c_fls := false.

  Notation tlit := (@tacLit sig fm_model).
  Notation tfun := (@tacFun sig _).

  Definition eq_t (t: term) (t': term) : bool := 
    eq_term t t'.

  Definition is_bool_t (t: term) : bool := 
    orb (eq_term t c_tru) (eq_term t c_fls).


  MetaCoq Quote Definition c_zpos := Zpos.
  MetaCoq Quote Definition c_zneg := Zneg.
  MetaCoq Quote Definition c_z0 := Z0.

  Definition is_z_t (t: term) : bool :=
    match t with 
    | tApp t' _ => 
      orb (eq_term t' c_zpos) (eq_term t' c_zneg)
    | _ => eq_term t c_z0
    end.

  Program Definition match_tacs : list ((term -> bool) * tac_syn sig fm_model) := [
        (eq_t c_lt, tfun {| deep_f := Lt |})
      ; (eq_t c_le,  tfun {| deep_f := Lte |})
      ; (eq_t c_minus, tfun {| deep_f := Sub |})
      ; (is_bool_t, tlit bool_lit (fun b => existT _ BS b) (fun b _ => existT _ BS (TFun _ (BLit b) hnil)))
      ; (is_z_t, tlit z_lit (fun z => existT _ ZS z) (fun z _ => existT _ ZS (TFun _ (ZLit z) hnil)))
    ]. 

  MetaCoq Quote Definition bool_ind := (bool).
  MetaCoq Quote Definition z_ind := (Z).

  Definition match_inds : list (term * sorts) := [
        (bool_ind, BS)
      ; (z_ind, ZS)
    ].

  (* configure backend *)

  Declare ML Module "mirrorsolve".

  RegisterSMTSort BS SBool.
  RegisterSMTSort ZS SInt.

  RegisterSMTFun Lt "<" 2.
  RegisterSMTFun Lte "<=" 2.
  RegisterSMTFun Sub "-" 2.

  RegisterSMTBuiltin BLit BoolLit.
  RegisterSMTBuiltin ZLit IntLit.

  Require Import MirrorSolve.Axioms.

  Import UnsoundAxioms.

  MetaCoq Quote Definition mccarthy_vc := (forall v : Z,
    (100 <? v)%Z = true /\
    ((100 <? v)%Z = true -> (v - 10)%Z = (v - 10)%Z) /\
    ((v <=? 100)%Z = true -> (v - 10)%Z = 91%Z) \/
    (100 <? v)%Z <> true /\
    (forall rhs rhs0 : Z,
    ((100 <? rhs0)%Z = true -> rhs = (rhs0 - 10)%Z) /\
    ((rhs0 <=? 100)%Z = true -> rhs = 91%Z) ->
    ((100 <? rhs0)%Z = true -> rhs = (rhs0 - 10)%Z) /\
    ((rhs0 <=? 100)%Z = true -> rhs = 91%Z))).

  Goal forall st st',
    semantics mccarthy st st' -> 
    mc_post st'.
  Proof.
    intros.
    eapply wp_spec; eauto.
    clear H.
    simpl wp.
    unfold BoogieInd.put, BoogieInd.get, mc_post.
    simpl.
    generalize (st _ McCarthy91.N).
    simpl.
    setoid_rewrite <- Z.ltb_lt.
    setoid_rewrite <- Z.leb_le.
    Transparent denote_tm.
    match goal with 
    | |- ?G => 
      eapply denote_extract_specialized with (s := sig) (m := fm_model) (sorts_eq_dec := sorts_eq_dec) (match_tacs := match_tacs) (match_inds := match_inds) (p' := G) (t := mccarthy_vc)
    end.

    simpl_denote_tm.
    simpl_extract_tm.
    discharge_equiv_denote_orig; autorewrite with mod_fns in *; intuition eauto.
    specialize (H x).
    destruct H; [left | right]; 
    discharge_equiv_denote_orig; autorewrite with mod_fns in *; intuition eauto.
    
    let v' := fresh "v" in 
    let f' := fresh "f" in 
    match goal with 
    | |- interp_fm ?v ?f => 
      set (v' := v);
      set (f' := f)
    end;
    vm_compute in f';
    subst v';
    subst f'.

    match goal with 
    | |- ?G => check_interp_pos G; eapply interp_true
    end.

  Qed.

End McCarthy91.
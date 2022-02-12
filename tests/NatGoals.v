Require Import MirrorSolve.FirstOrder.

Require Import MirrorSolve.N.
Require Import MirrorSolve.Z.

Require Import MirrorSolve.N2Z.
Require Import MirrorSolve.SMT.

Require Import MirrorSolve.HLists.
Require Import Coq.Lists.List.

Import HListNotations.
Import ListNotations.

Require Import Coq.Strings.String.

Require Import MirrorSolve.Reflection.Core.
Require Import MirrorSolve.Reflection.FM.

Notation bop o l r := (TFun N.sig o (l ::: r ::: hnil)).
Notation nlit n := (TFun N.sig (N.NLit n) hnil).

MetaCoq Quote Definition c_plus := @plus.
MetaCoq Quote Definition c_times := @Nat.mul.
MetaCoq Quote Definition c_sub := @Nat.sub.
MetaCoq Quote Definition c_div := @Nat.div.
MetaCoq Quote Definition c_mod := @Nat.modulo.
MetaCoq Quote Definition c_lte := @Nat.leb.
MetaCoq Quote Definition c_lt := @Nat.ltb.
(* 
MetaCoq Unquote Definition reif_lt := (c_lt).
Print reif_lt. *)

(* MetaCoq Quote Definition c_gte := @Nat.geb.
MetaCoq Quote Definition c_gt := @Nat.gtb. *)

MetaCoq Quote Definition c_tru := true.
MetaCoq Quote Definition c_fls := false.
MetaCoq Quote Definition c_zero := 0.
MetaCoq Quote Definition c_succ := S.

Definition term2bool (t: term) : option bool := 
  if eq_term t c_tru then Some true
  else if eq_term t c_fls then Some false
  else None.

Fixpoint term2nat (t: term) : option nat := 
  if eq_term t c_zero then Some 0 
  else 
    match t with 
    | tApp f [e'] => 
      if eq_term f c_succ then 
        match term2nat e' with 
        | Some n' => Some (S n')
        | _ => None
        end
      else 
        None
    | _ => None
    end.

Obligation Tactic := intros.
Equations extract_t2tm {c: ctx N.sig} (t: term) (r_args: list (option ({srt & N.tm c srt}))) : option ({srt & N.tm c srt}) := 
  extract_t2tm (tApp f es) r_args := 
    match r_args with 
    | [Some l; Some r] => 
      let (sl, tl) := l in
      let (sr, tr) := r in 
      match sl as sl', sr as sr' return N.tm c sl' -> N.tm c sr' -> option ({srt & N.tm c srt}) with
      | NS, NS => fun tl' tr' => 
        if eq_term f c_plus then 
          Some (existT _ _ (TFun N.sig N.Plus (tl' ::: tr' ::: hnil)))
        else if eq_term f c_times then 
          Some (existT _ _ (TFun N.sig N.Mul (tl' ::: tr' ::: hnil)))
        else if eq_term f c_sub then 
          Some (existT _ _ (TFun N.sig N.Sub (tl' ::: tr' ::: hnil)))
        else if eq_term f c_mod then 
          Some (existT _ _ (TFun N.sig N.Mod (tl' ::: tr' ::: hnil)))
        else if eq_term f c_div then 
          Some (existT _ _ (TFun N.sig N.Div (tl' ::: tr' ::: hnil)))
        else if eq_term f c_lte then 
          Some (existT _ _ (TFun N.sig N.Lte (tl' ::: tr' ::: hnil)))
        else if eq_term f c_lt then 
          Some (existT _ _ (TFun N.sig N.Lt (tl' ::: tr' ::: hnil)))
        (* else if eq_term f c_gte then 
          Some (existT _ _ (TFun N.sig N.Gte (tl' ::: tr' ::: hnil)))
        else if eq_term f c_gt then 
          Some (existT _ _ (TFun N.sig N.Gt (tl' ::: tr' ::: hnil))) *)
        else 
          None
      | _, _ => fun _ _ => None
      end tl tr
    | _ => 
      match term2nat (tApp f es) with 
      | Some n => Some (existT _ _ (TFun N.sig (N.NLit n) hnil))
      | None => None
      end
    end;
  extract_t2tm (tConstruct ind i x) _ := 
    let t := (tConstruct ind i x) in 
    match term2bool t with 
    | Some b => Some (existT _ _ (TFun N.sig (N.BLit b) hnil))
    | None =>
      match term2nat t with 
      | Some n => Some (existT _ _ (TFun N.sig (N.NLit n) hnil))
      | None => None
      end
    end;
  extract_t2tm _ _ := None.

MetaCoq Quote Definition nat_ind := (nat).
MetaCoq Quote Definition bool_ind := (bool).

Definition get_ind (t: term) : option inductive := 
  match t with 
  | tInd x _ => Some x
  | _ => None
  end.

Definition nat_ind' : inductive.
  set (foo := get_ind nat_ind).
  compute in foo.
  match goal with 
  | _ := Some ?X |- _ => exact X
  end.
Defined.
Definition bool_ind' : inductive.
  set (foo := get_ind bool_ind).
  compute in foo.
  match goal with 
  | _ := Some ?X |- _ => exact X
  end.
Defined.

Definition ind2srt (i: inductive) : option N.sorts := 
  if eq_inductive i nat_ind' then Some N.NS
  else if eq_inductive i bool_ind' then Some N.BS
  else None.

MetaCoq Quote Definition test := (forall (n: nat), true = true).
Definition test' : (FirstOrder.fm N.sig (SLNil _)).
  set (foo := extract_t2fm N.sig (@extract_t2tm) ind2srt N.sorts_eq_dec (SLNil _) 0 test).
  vm_compute in foo.
  match goal with 
  | _ := Some ?X |- _ => exact X
  end.
Defined.

MetaCoq Quote Definition test_2 := 
  (forall n m, n <> 0 -> m * m = 2 * n * n -> Nat.ltb m (2 * n) = true).

Definition test_2' : (FirstOrder.fm N.sig (SLNil _)).
  set (foo := extract_t2fm N.sig (@extract_t2tm) ind2srt N.sorts_eq_dec (SLNil _) 0 test_2).
  vm_compute in foo.
  match goal with 
  | _ := Some ?X |- _ => exact X
  end.
Defined.

Declare ML Module "mirrorsolve".

RegisterSMTSort ZS SInt.
RegisterSMTSort BS SBool.

RegisterSMTFun Z.Plus "+" 2.
RegisterSMTFun Z.Gte ">=" 2.
RegisterSMTFun Z.Lt "<" 2.
RegisterSMTFun Z.Mul "*" 2.

RegisterSMTBuiltin Z.BLit BoolLit.
RegisterSMTBuiltin Z.ZLit IntLit.


  (* forall n m, n <> 0 -> m * m = 2 * n * n -> m < 2 * n
   *)

Require Import Coq.Program.Equality.

Inductive reif_ty := | TNat | TBool.

Scheme Equality for reif_ty.

Definition interp_rty rty := 
  match rty with 
  | TNat => nat
  | TBool => bool
  end.

Equations reify_t2nt (t: term) (args: list (option ({ty & interp_rty ty}))) : option ({ty & interp_rty ty}) := 
  reify_t2nt (tApp f es) r_args := 
    match r_args with 
    | [Some l; Some r] => 
      let (sl, tl) := l in
      let (sr, tr) := r in 
      match sl as sl', sr as sr' return interp_rty sl' -> interp_rty sr' -> option ({ty & interp_rty ty}) with 
      | TNat, TNat => fun tl' tr' =>
        if eq_term f c_plus then 
          Some (existT _ TNat (tl' + tr'))
        else if eq_term f c_times then 
          Some (existT _ TNat (tl' * tr'))
        else if eq_term f c_sub then 
          Some (existT _ TNat (tl' - tr'))
        else if eq_term f c_mod then 
          Some (existT _ TNat (Nat.modulo tl' tr'))
        else if eq_term f c_div then 
          Some (existT _ TNat (Nat.div tl' tr'))
        else if eq_term f c_lte then 
          Some (existT _ TBool (Nat.leb tl' tr'))
        else if eq_term f c_lt then 
          Some (existT _ TBool (Nat.ltb tl' tr'))
        (* else if eq_term f c_gte then 
          Some (existT _ TNat (TFun N.sig N.Gte (tl' ::: tr' ::: hnil)))
        else if eq_term f c_gt then 
          Some (existT _ TNat (TFun N.sig N.Gt (tl' ::: tr' ::: hnil))) *)
        else 
          None
      | _, _ => fun _ _ => None
      end tl tr
    | _ => 
      match term2nat (tApp f es) with 
      | Some n => Some (existT _ TNat n)
      | None => None
      end
    end;
  reify_t2nt (tConstruct ind i x) _ := 
    let t := (tConstruct ind i x) in 
    match term2bool t with 
    | Some b => Some (existT _ TBool b)
    | None =>
      match term2nat t with 
      | Some n => Some (existT _ TNat n)
      | None => None
      end
    end;
  reify_t2nt _ _ := None.

Definition reify_i2nty (i: inductive) : option reif_ty := 
  if eq_inductive i nat_ind' then Some TNat
  else if eq_inductive i bool_ind' then Some TBool
  else None.

Lemma some_prop: 
  forall p p': Prop,
  Some p = Some p' <-> 
  p = p'.
Proof.
  intros.
  split; intros; subst; trivial; inversion H; trivial.
Qed.

Lemma iff_distribute:
  forall a b c d : Prop,
    (a <-> c) -> 
    (b <-> d) -> 
    ((a -> b) <-> (c -> d)).
Proof.
  intros.
  erewrite H.
  erewrite H0.
  eapply iff_refl.
Qed.



Theorem reify_extract t:
  forall (p p': Prop) fm,
    reify_t2fm reif_ty interp_rty reif_ty_eq_dec reify_t2nt reify_i2nty (SLNil _) 0 t = Some p -> 
    extract_t2fm N.sig (@extract_t2tm) ind2srt N.sorts_eq_dec (SLNil _) 0 t = Some fm -> 
    (p <-> p') ->
    (p' <-> interp_fm (VEmp _ N.fm_model) fm).
Proof.

  induction t; intros; try now (
    simpl in H;
    inversion H
  ).
  -
    simpl in H.
    simpl in H0.
    destruct (binder_name na) eqn:?.
    + simpl in *.
      (* Notice that the recursion modifies the environment here. We need a stronger theorem that describes the translation environment as well. *)
      assert (0 = 1) by admit. 
      erewrite <- H2 in *.
      clear H2.
      erewrite <- H1 in *.
      repeat match goal with 
      | H: (match ?X with | _ => _ end) = _ |- _ => 
        destruct X; [| inversion H]
      end.
      repeat match goal with 
      | H: Some _ = Some _ |- _ => 
        erewrite some_prop in H; subst
      | H: Some _ = Some _ |- _ => 
        inversion H; subst
      end.
      
      (* clear H1. *)
      clear H0.

      autorewrite with interp_fm.
      eapply iff_distribute.
      * eapply IHt1; [exact eq_refl | |eapply iff_refl]; trivial.
      * eapply IHt2; [exact eq_refl | |eapply iff_refl]; trivial.
    + admit.
  - admit.
  - simpl in H.
    simpl in H0.
    destruct (eq_term _ _); [
      inversion H;
      inversion H0;
      subst;
      erewrite H1;
      eapply iff_refl
    |].
    destruct (eq_term _ _); [
      inversion H;
      inversion H0;
      subst;
      erewrite H1;
      eapply iff_refl
    |].
    inversion H.
  - simpl in H.
    simpl in H0.
    destruct (eq_term _ _); [
      inversion H;
      inversion H0;
      subst;
      erewrite H1;
      eapply iff_refl
    |].
    inversion H.
Admitted. 

MetaCoq Test Quote (let x := 2 in x).

Goal (forall n m, n <> 0 -> m * m = 2 * n * n -> Nat.ltb m (2 * n) = true).
Proof.
  match goal with 
  | |- ?G => 
    eapply reify_extract with (p' := G) (t := test_2)
  end.
  1: {
  set (x := reify_t2fm _ _ _ _ _ _ _ _).
    simpl in x.
    Transparent reify_t2nt.
    unfold reify_t2nt in x.
    Transparent term2bool.
    Transparent term2nat.
    simpl in x.
    unfold eq_rect_r in x.
    simpl in x.
    exact eq_refl.
  }
  1: {
    set (foo := extract_t2fm _ _ _ _ _ _ _).
    vm_compute in foo.
    exact eq_refl.
  }
    
  - split; 
    intros.
    + 
      repeat match goal with 
      | H: forall (_: ?T), exists _, _ |- _ =>
        let v := fresh "v" in 
        evar (v: T);
        specialize (H v);
        subst v
      | H: _ /\ _ |- _ => 
        destruct H
      | H: exists _, _ |- _ => 
        destruct H
      | H: Some _ = Some _ |- _ => 
        erewrite some_prop in H
      | H: _ = ?X |- _ => subst X
      end.
      intuition.
    +
      repeat match goal with
      | |- exists _: Prop, _ => eexists
      | |- _ /\ _ => split
      | |- Some _ = Some _ => exact eq_refl
      | |- _ => intros
      end.
      intuition.
  - 
    eapply n2z_corr.
    match goal with 
    | |- interp_fm ?v ?f => 
      set (v' := v);
      set (f' := f)
    end.
    vm_compute in f'.
    subst v'.

    unfold n2z_func.
    autorewrite with fmap_valu.
    subst f'.

    match goal with 
    | |- ?G => 
      check_interp_pos G; admit
    end.
Admitted.
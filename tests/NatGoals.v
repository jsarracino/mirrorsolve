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
Equations reflect_t2tm {c: ctx N.sig} (t: term) (r_args: list (option ({srt & N.tm c srt}))) : option ({srt & N.tm c srt}) := 
  reflect_t2tm (tApp f es) r_args := 
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
  reflect_t2tm (tConstruct ind i x) _ := 
    let t := (tConstruct ind i x) in 
    match term2bool t with 
    | Some b => Some (existT _ _ (TFun N.sig (N.BLit b) hnil))
    | None =>
      match term2nat t with 
      | Some n => Some (existT _ _ (TFun N.sig (N.NLit n) hnil))
      | None => None
      end
    end;
  reflect_t2tm _ _ := None.

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
  set (foo := reflect_t2fm N.sig (@reflect_t2tm) ind2srt N.sorts_eq_dec (SLNil _) 0 test).
  vm_compute in foo.
  match goal with 
  | _ := Some ?X |- _ => exact X
  end.
Defined.

MetaCoq Quote Definition test_2 := 
  (forall n m, n <> 0 -> m * m = 2 * n * n -> Nat.ltb m (2 * n) = true).

Definition test_2' : (FirstOrder.fm N.sig (SLNil _)).
  set (foo := reflect_t2fm N.sig (@reflect_t2tm) ind2srt N.sorts_eq_dec (SLNil _) 0 test_2).
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
(* 
Lemma nat_square_decreasing : 
  interp_fm (sig := N.sig) (VEmp _ N.fm_model) (FForall (sig :=  N.sig) NS (FForall (sig :=  N.sig) NS (
    FImpl (FNeg _ (FEq 
      (TVar (VThere _ _ _ _ (VHere _ _ _)))
      (nlit 0)
      ))
    (FImpl (FEq 
      (bop N.Mul (TVar (VHere _ _ _)) (TVar ((VHere _ _ _))))
      (bop N.Mul (nlit 2) (bop N.Mul (TVar (VThere _ _ _ _ (VHere _ _ _))) (TVar (VThere _ _ _ _ (VHere _ _ _))))))
    (FEq tru
      (bop N.Lt (TVar (VHere _ _ _)) (bop N.Mul (nlit 2) (TVar (VThere _ _ _ _ (VHere _ _ _)))))
    ))
  ))).
Proof.
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
Admitted. *)

Lemma nat_square_decreasing' : 
  interp_fm (sig := N.sig) (VEmp _ N.fm_model) test_2'.
Proof.
  unfold test_2'.
  repeat (
    intros || 
    autorewrite with interp_tm in * ||
    autorewrite with mod_fns in * ||
    autorewrite with interp_fm in * 
  ).
  autorewrite with find in H.
  autorewrite with find in H0.
  autorewrite with find.
  Restart.

  unfold test_2'.
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

Require Import Coq.Program.Equality.

Inductive reif_ty := | TNat | TBool.

Scheme Equality for reif_ty.

Check reif_ty_eq_dec.

Definition interp_rty rty := 
  match rty with 
  | TNat => nat
  | TBool => bool
  end.

Equations parse_t2nt (t: term) (args: list (option ({ty & interp_rty ty}))) : option ({ty & interp_rty ty}) := 
  parse_t2nt (tApp f es) r_args := 
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
  parse_t2nt (tConstruct ind i x) _ := 
    let t := (tConstruct ind i x) in 
    match term2bool t with 
    | Some b => Some (existT _ TBool b)
    | None =>
      match term2nat t with 
      | Some n => Some (existT _ TNat n)
      | None => None
      end
    end;
  parse_t2nt _ _ := None.

Definition parse_i2nty (i: inductive) : option reif_ty := 
  if eq_inductive i nat_ind' then Some TNat
  else if eq_inductive i bool_ind' then Some TBool
  else None.


Theorem parse_reflect :
  forall t p (p': Prop) fm,
    parse_t2fm reif_ty interp_rty reif_ty_eq_dec parse_t2nt parse_i2nty (SLNil _) 0 t = Some p -> 
    reflect_t2fm N.sig (@reflect_t2tm) ind2srt N.sorts_eq_dec (SLNil _) 0 t = Some fm -> 
    (p <-> p') ->
    (p' <-> interp_fm (VEmp _ N.fm_model) fm).
Admitted.

Goal (forall n m, n <> 0 -> m * m = 2 * n * n -> Nat.ltb m (2 * n) = true).
Proof.
  match goal with 
  | |- ?G => 
    eapply parse_reflect with (p' := G) (t := test_2)
  end.
  - set (x := parse_t2fm _ _ _ _ _ _ _ _).
    simpl in x.
    Transparent parse_t2nt.
    unfold parse_t2nt in x.
    Transparent term2bool.
    Transparent term2nat.
    simpl in x.
    unfold eq_rect_r in x.
    simpl in x.
    exact eq_refl.
  - 
    set (foo := reflect_t2fm _ _ _ _ _ _ _).
    vm_compute in foo.
    exact eq_refl.
  - split; 
    intros.
    + 
      specialize (H n).
      destruct H.
      destruct H.
      assert (x = (
        forall x : nat,
        exists p' : Prop,
      Some
        (n <> 0 ->
        x * x = (n + (n + 0)) * n ->
        Nat.ltb x (n + (n + 0)) = true) =
      Some p' /\ p')) by admit.
      subst x.
      
      specialize (H2 m).
      destruct H2.
      assert (x = (n <> 0 ->
      m * m = (n + (n + 0)) * n ->
      Nat.ltb m (n + (n + 0)) = true)) by admit.
      destruct H2.
      subst x.
      clear H.
      clear H2.
      eauto.
    +
      eexists.
      intros.
      eexists.
      * exact eq_refl.
      * 
        intros.
        eexists.
        split; [exact eq_refl|].
        intros.
        eapply H; auto.
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
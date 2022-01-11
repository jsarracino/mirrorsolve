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
      match sl as sl' return (N.tm c sl' -> N.tm c sr -> option ({srt & N.tm c srt})) with
      | NS => 
        match sr as sr' return (N.tm c NS -> N.tm c sr' -> option ({srt & N.tm c srt})) with
        | NS => fun tl' tr' => 
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
        | _ => fun _ _ => None
        end
      | _ => fun _ _ => None
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
Definition test' : (FirstOrder.fm N.sig (CEmp N.sig)).
  set (foo := reflect_t2fm N.sig (@reflect_t2tm) ind2srt N.sorts_eq_dec (CEmp _) 0 test).
  vm_compute in foo.
  match goal with 
  | _ := Some ?X |- _ => exact X
  end.
Defined.

MetaCoq Quote Definition test_2 := (forall n m, n <> 0 -> m * m = 2 * n * n -> Nat.ltb m (2 * n) = true).

Definition test_2' : (FirstOrder.fm N.sig (CEmp N.sig)).
  set (foo := reflect_t2fm N.sig (@reflect_t2tm) ind2srt N.sorts_eq_dec (CEmp _) 0 test_2).
  vm_compute in foo.
  match goal with 
  | _ := Some ?X |- _ => exact X
  end.
Defined.

Print test_2'.

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
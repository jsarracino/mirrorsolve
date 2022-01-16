
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import MirrorSolve.FirstOrder.

Require Import MetaCoq.Template.All.
Require Import MirrorSolve.Reflection.Core.
Set Universe Polymorphism.

Require Import MirrorSolve.HLists.

MetaCoq Quote Definition c_True := True.
MetaCoq Quote Definition c_False := False.
MetaCoq Quote Definition c_eq := @eq.
MetaCoq Quote Definition c_not := @not.
MetaCoq Quote Definition c_or := @or.
MetaCoq Quote Definition c_and := @and.

Section ReflectFM.
  Variable (s: signature).
  Variable (m: model s).

  Variable (reflect_t2tm : forall c, term -> list (option ({srt & (tm s c srt)})) -> option ({srt & (tm s c srt)})).
  Variable (reflect_ind2srt : inductive -> option (sig_sorts s)).

  Variable (sort_eq_dec: EquivDec.EqDec (sig_sorts s) eq).

  Equations mk_var (c: ctx s) (n: nat) : option ({srt & var s c srt}) by struct n := 
    mk_var (Snoc _ c' srt) 0 := Some (existT _ srt (VHere _ _ srt));
    mk_var (Snoc _ c' srt) (S n') := 
      let nxt := mk_var c' n' in 
      match nxt with 
      | Some v =>
        let (ty', v') := v in 
        Some (existT _ ty' (VThere _ _ _ _ v'))
      | None => None
      end;
    mk_var SLNil _ := None.

  Fixpoint reflect_t2tm' (c: ctx s) (acc: nat) (t: term) : option ({srt & tm s c srt}) :=  
    match t with 
    | tRel n => 
      match mk_var c (n - acc) with 
      | Some (existT srt v) => 
        Some (existT _ srt (TVar v))
      | None => None
      end
    | tApp f es => reflect_t2tm c t (map (reflect_t2tm' c acc) es)
    | _ => reflect_t2tm c t []
    end.

  Obligation Tactic := intros.
  Equations reflect_t2fm (c: ctx s) (anon_acc: nat) (t: term) : option (fm _ c) by struct t := 
    reflect_t2fm c acc t := 
      if eq_term t c_True then Some FTrue else 
      if eq_term t c_False then Some FFalse else
      match t with
      | tApp f es => 
        if eq_term f c_eq then 
          match es with 
          | _ :: tl :: tr :: _ => 
            match reflect_t2tm' c acc tl, reflect_t2tm' c acc tr with 
            | Some l, Some r => 
              let (sl, el) := l in 
              let (sr, er) := r in 
                match sort_eq_dec sl sr with 
                | left HEq => 
                  Some (FEq el (eq_rect_r _ er HEq))
                | _ => None
                end
            | _, _ => None
            end
          | _ => None
          end
        else if eq_term f c_or then 
          match es with 
          | tl :: tr :: _ => 
            match reflect_t2fm c acc tl, reflect_t2fm c acc tr with 
            | Some l, Some r => Some (@FOr _ c l r)
            | _, _ => None
            end
          | _ => None
          end
        else if eq_term f c_and then 
          match es with 
          | tl :: tr :: _ => 
            match reflect_t2fm c acc tl, reflect_t2fm c acc tr with 
            | Some l, Some r => Some (@FAnd _ c l r)
            | _, _ => None
            end
          | _ => None
          end
        else if eq_term f c_not then 
          match es with 
          | x :: _ => 
            match reflect_t2fm c acc x with 
            | Some x' => Some (FNeg _ x')
            | None => None
            end
          | _ => None
          end
        else
          None
      | tProd ba_name pre pst => 
        match ba_name.(binder_name) with 
        | nAnon => 
          match reflect_t2fm c acc pre, reflect_t2fm c (S acc) pst with 
          | Some el, Some er => Some (FImpl el er)
          | _, _ => None
          end
        | nNamed _ => 
          match pre with 
          | tInd i _ => 
            let srt := reflect_ind2srt i in 
            match srt with 
            | Some srt => 
              let c' := Snoc _ c srt in
              let inner := reflect_t2fm c' acc pst in 
              match inner with 
              | Some fm => Some (FForall _ fm)
              | None => None
              end
              
            | None => None
            end
          | _ => None
          end
        end
      | _ => None
      end.

  (* TODO: soundness lemma; forall c t fm, reflect_t2fm c t = Some fm -> (forall v, interp_coq_tm v t <-> interp_fm v fm) *)

  (* Some light tests *)
  (* Variable (c: ctx s).

  MetaCoq Quote Definition test_1 := (False -> True).
  MetaCoq Quote Definition test_2 := (True = False -> False).
  MetaCoq Quote Definition test_3 := (~ ~ False).
  MetaCoq Quote Definition test_4 := (False /\ True).
  MetaCoq Quote Definition test_5 := (forall (x: unit), True).
  MetaCoq Quote Definition test_6 := (forall (x: unit), True \/ False \/ ~ True).

  Eval vm_compute in reflect_t2fm c 0 test_1.
  Eval vm_compute in reflect_t2fm c 0 test_2. 
  Eval vm_compute in reflect_t2fm c 0 test_3.
  Eval vm_compute in reflect_t2fm c 0 test_4.
  Eval vm_compute in reflect_t2fm c 0 test_5.
  Eval vm_compute in reflect_t2fm c 0 test_6. *)
End ReflectFM.
    



Section ParseFM.
  Variable (Ty: Type).
  Variable (interp_ty: Ty -> Type).

  Variable (ty_eq_dec: EquivDec.EqDec Ty eq).

  Notation res_ty := (option ({ty & interp_ty ty})).
  Notation env_ty := (snoc_list ({ty & interp_ty ty})).

  Variable (parse_t2tm : term -> list res_ty -> res_ty).
  Variable (parse_ind : inductive -> option Ty).

  Fixpoint parse_var (env: env_ty) (n: nat) : res_ty :=
    match env, n with 
    | Snoc _ x, 0 => Some x
    | Snoc env' _, S n' => parse_var env' n'
    | SLNil, _ => None
    end.

  Fixpoint parse_t2tm' (env: env_ty) (acc: nat) (t: term) : res_ty :=  
    match t with 
    | tRel n => parse_var env (n - acc)
    | tApp f es => parse_t2tm t (map (parse_t2tm' env acc) es)
    | _ => parse_t2tm t []
    end.

  Definition ret (p: Prop) : option (env_ty -> option Prop) := Some (fun _ => Some p).

  Obligation Tactic := intros.
  Equations parse_t2fm (env: env_ty) (anon_acc: nat) (t: term) : option Prop by struct t := 
    parse_t2fm env acc t := 
      if eq_term t c_True then Some True else 
      if eq_term t c_False then Some False else
      match t with
      | tApp f es => 
        if eq_term f c_eq then 
          match es with 
          | _ :: tl :: tr :: _ => 
            match parse_t2tm' env acc tl, parse_t2tm' env acc tr with 
            | Some l, Some r => 
              let (tl, el) := l in 
              let (tr, er) := r in 
                match ty_eq_dec tl tr with 
                | left HEq => 
                  Some (el = (eq_rect_r _ er HEq))
                | _ => None
                end
            | _, _ => None
            end
          | _ => None
          end
        else if eq_term f c_or then 
          match es with 
          | tl :: tr :: _ => 
            match parse_t2fm env acc tl, parse_t2fm env acc tr with 
            | Some l, Some r => Some (l \/ r)
            | _, _ => None
            end
          | _ => None
          end
        else if eq_term f c_and then 
          match es with 
          | tl :: tr :: _ => 
            match parse_t2fm env acc tl, parse_t2fm env acc tr with 
            | Some l, Some r => Some (l /\ r)
            | _, _ => None
            end
          | _ => None
          end
        else if eq_term f c_not then 
          match es with 
          | x :: _ => 
            match parse_t2fm env acc x with 
            | Some x' => Some (~ x')
            | None => None
            end
          | _ => None
          end
        else
          None
      | tProd ba_name pre pst => 
        match ba_name.(binder_name) with 
        | nAnon =>
          match parse_t2fm env acc pre, parse_t2fm env (S acc) pst with 
          | Some el, Some er => Some (el -> er)
          | _, _ => None
          end
        | nNamed _ =>
          match pre with 
          | tInd i _ => 
            let ty := parse_ind i in 
            match ty with
            | Some ty' => Some (
              forall x: interp_ty ty', 
              exists p',
              let env' := Snoc _ env (existT _ ty' x) in
                  parse_t2fm env' acc pst = Some p' /\
                  p'
              )
            | None => None
            end
          | _ => None
          end
        end
      | _ => None
      end.

  (* MetaCoq Quote Definition test_1 := (False -> True).
  MetaCoq Quote Definition test_2 := (True = False -> False).
  MetaCoq Quote Definition test_3 := (~ ~ False).
  MetaCoq Quote Definition test_4 := (False /\ True).
  MetaCoq Quote Definition test_5 := (forall (x: unit), x = tt).
  MetaCoq Quote Definition test_6 := (forall (x: unit), True \/ False \/ ~ True).

  Eval vm_compute in parse_t2fm (SLNil _)  0 test_1.
  Eval vm_compute in parse_t2fm (SLNil _)  0 test_2. 
  Eval vm_compute in parse_t2fm (SLNil _)  0 test_3.
  Eval vm_compute in parse_t2fm (SLNil _)  0 test_4.
  Eval vm_compute in parse_t2fm (SLNil _)  0 test_5.
  Eval vm_compute in parse_t2fm (SLNil _)  0 test_6. *)
End ParseFM.
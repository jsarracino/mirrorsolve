
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import MirrorSolve.FirstOrder.

Require Import MetaCoq.Template.All.
Require Import MirrorSolve.Reflection.Core.
Set Universe Polymorphism.

Section ReflectFM.
  Variable (s: signature).
  Variable (m: model s).

  Variable (reflect_t2tm : forall c, term -> list (option ({srt & (tm s c srt)})) -> option ({srt & (tm s c srt)})).
  Variable (reflect_ind2srt : inductive -> option (sig_sorts s)).

  Variable (sort_eq_dec: EquivDec.EqDec (sig_sorts s) eq).

  Equations mk_var (c: ctx s) (n: nat) : option ({srt & var s c srt}) by struct n := 
    mk_var (CSnoc c' srt) 0 := Some (existT _ srt (VHere _ _ srt));
    mk_var (CSnoc c' srt) (S n') := 
      let nxt := mk_var c' n' in 
      match nxt with 
      | Some v =>
        let (srt', v') := v in 
        Some (existT _ srt' (VThere _ _ _ _ v'))
      | None => None
      end;
    mk_var CEmp _ := None.

  MetaCoq Quote Definition c_True := True.
  MetaCoq Quote Definition c_False := False.
  MetaCoq Quote Definition c_eq := @eq.
  MetaCoq Quote Definition c_not := @not.
  MetaCoq Quote Definition c_or := @or.
  MetaCoq Quote Definition c_and := @and.

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
              let c' := CSnoc _ c srt in
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
  MetaCoq Quote Definition test_4 := (False).
  MetaCoq Quote Definition test_5 := (forall (x: unit), True).
  MetaCoq Quote Definition test_6 := (forall (x: unit), True \/ False \/ ~ True).

  Eval vm_compute in reflect_t2fm c test_1.
  Eval vm_compute in reflect_t2fm c test_2. 
  Eval vm_compute in reflect_t2fm c test_3.
  Eval vm_compute in reflect_t2fm c test_4.
  Eval vm_compute in reflect_t2fm c test_5.
  Eval vm_compute in reflect_t2fm c test_6. *)
End ReflectFM.
    
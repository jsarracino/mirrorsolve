
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

Section ExtractFM.
  Variable (s: signature).
  Variable (m: model s).

  Variable (extract_t2tm : forall c, term -> list (option ({srt & (tm s c srt)})) -> option ({srt & (tm s c srt)})).
  Variable (extract_ind2srt : inductive -> option (sig_sorts s)).

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

  Fixpoint extract_t2tm' (c: ctx s) (acc: nat) (t: term) : option ({srt & tm s c srt}) :=  
    match t with 
    | tRel n => 
      match mk_var c (n - acc) with 
      | Some (existT srt v) => 
        Some (existT _ srt (TVar v))
      | None => None
      end
    | tApp f es => extract_t2tm c t (map (extract_t2tm' c acc) es)
    | _ => extract_t2tm c t []
    end.

  Obligation Tactic := intros.
  Equations extract_t2fm (c: ctx s) (anon_acc: nat) (t: term) : option (fm _ c) by struct t := 
    extract_t2fm c acc t := 
      if eq_term t c_True then Some FTrue else 
      if eq_term t c_False then Some FFalse else
      match t with
      | tApp f es => 
        if eq_term f c_eq then 
          match es with 
          | _ :: tl :: tr :: _ => 
            match extract_t2tm' c acc tl, extract_t2tm' c acc tr with 
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
            match extract_t2fm c acc tl, extract_t2fm c acc tr with 
            | Some l, Some r => Some (@FOr _ c l r)
            | _, _ => None
            end
          | _ => None
          end
        else if eq_term f c_and then 
          match es with 
          | tl :: tr :: _ => 
            match extract_t2fm c acc tl, extract_t2fm c acc tr with 
            | Some l, Some r => Some (@FAnd _ c l r)
            | _, _ => None
            end
          | _ => None
          end
        else if eq_term f c_not then 
          match es with 
          | x :: _ => 
            match extract_t2fm c acc x with 
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
          match extract_t2fm c acc pre, extract_t2fm c (S acc) pst with 
          | Some el, Some er => Some (FImpl el er)
          | _, _ => None
          end
        | nNamed _ => 
          match pre with 
          | tInd i _ => 
            let srt := extract_ind2srt i in 
            match srt with 
            | Some srt => 
              let c' := Snoc _ c srt in
              let inner := extract_t2fm c' acc pst in 
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

  (* TODO: soundness lemma; forall c t fm, extract_t2fm c t = Some fm -> (forall v, interp_coq_tm v t <-> interp_fm v fm) *)

  (* Some light tests *)
  (* Variable (c: ctx s).

  MetaCoq Quote Definition test_1 := (False -> True).
  MetaCoq Quote Definition test_2 := (True = False -> False).
  MetaCoq Quote Definition test_3 := (~ ~ False).
  MetaCoq Quote Definition test_4 := (False /\ True).
  MetaCoq Quote Definition test_5 := (forall (x: unit), True).
  MetaCoq Quote Definition test_6 := (forall (x: unit), True \/ False \/ ~ True).

  Eval vm_compute in extract_t2fm c 0 test_1.
  Eval vm_compute in extract_t2fm c 0 test_2. 
  Eval vm_compute in extract_t2fm c 0 test_3.
  Eval vm_compute in extract_t2fm c 0 test_4.
  Eval vm_compute in extract_t2fm c 0 test_5.
  Eval vm_compute in extract_t2fm c 0 test_6. *)
End ExtractFM.
    



Section DenoteFM.

  Variable (s: signature).
  Variable (m: model s).

  Variable (sorts_eq_dec: EquivDec.EqDec (s.(sig_sorts)) eq).

  Notation res_ty := ({ty & option (s.(mod_sorts) m ty)}).
  (* Notation env_ty := ({c & valu s m c}). *)
  Notation env_ty c := (valu s m c).

  Variable (denote_tm : term -> list res_ty -> res_ty).
  Variable (reify_ind : inductive -> option (s.(sig_sorts))).

  Variable (default_ty : s.(sig_sorts)).

  Fixpoint denote_var {c} (env: env_ty c) (n: nat) : res_ty :=
    match env, n with 
    | VSnoc _ _ _ x, 0 => (existT _ _ (Some x))
    | VSnoc _ _ env' _, S n' => denote_var env' n'
    | VEmp, _ => existT _ default_ty None
    end.

  Fixpoint denote_tm' {c} (env: env_ty c) (acc: nat) (t: term) : res_ty :=  
    match t with 
    | tRel n => denote_var env (n - acc)
    | tApp f es => denote_tm t (map (denote_tm' env acc) es)
    | _ => denote_tm t []
    end.

  Definition pure {c} (p: Prop) : option (env_ty c -> Prop) := Some (fun _ => p).

  Obligation Tactic := intros.
  Equations denote_t2fm {c} (anon_acc: nat) (t: term) : option (env_ty c -> Prop) by struct t := 
    denote_t2fm acc t := 
      if eq_term t c_True then pure True else 
      if eq_term t c_False then pure False else
      match t with
      | tApp f es => 
        if eq_term f c_eq then 
          match es with 
          | _ :: tl :: tr :: _ => Some (fun env =>
            let (tl, el) := denote_tm' env acc tl in 
            let (tr, er) := denote_tm' env acc tr in 
            match sorts_eq_dec tl tr with 
            | left HEq =>
              match el, er with 
              | Some l, Some r => 
                l = (eq_rect_r _ r HEq)
              | _, _ => False
              end
            | _ => False
            end)
          | _ => None
          end
        (* else if eq_term f c_or then 
          match es with 
          | tl :: tr :: _ => 
            match denote_t2fm env acc tl, denote_t2fm env acc tr with 
            | Some l, Some r => Some (l \/ r)
            | _, _ => None
            end
          | _ => None
          end
        else if eq_term f c_and then 
          match es with 
          | tl :: tr :: _ => 
            match denote_t2fm env acc tl, denote_t2fm env acc tr with 
            | Some l, Some r => Some (l /\ r)
            | _, _ => None
            end
          | _ => None
          end
        else if eq_term f c_not then 
          match es with 
          | x :: _ => 
            match denote_t2fm env acc x with 
            | Some x' => Some (~ x')
            | None => None
            end
          | _ => None
          end *)
        else
          None
      | tProd ba_name pre pst => 
        match ba_name.(binder_name) with 
        | nAnon =>
          match denote_t2fm acc pre, denote_t2fm (S acc) pst with 
          | Some el, Some er => Some (fun env => (el env -> er env))
          | _, _ => None
          end
        | nNamed _ =>
          match pre with 
          | tInd i _ => 
            let ty := reify_ind i in 
            match ty with
            | Some ty' => 
              match denote_t2fm acc pst with 
              | Some p => Some ( fun env => 
                forall x: (s.(mod_sorts) m ty'),
                  let env' := VSnoc _ _ ty' c env x in 
                    p env'
                )
              | None => None
              end
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

  Eval vm_compute in denote_t2fm (SLNil _)  0 test_1.
  Eval vm_compute in reify_t2fm (SLNil _)  0 test_2. 
  Eval vm_compute in reify_t2fm (SLNil _)  0 test_3.
  Eval vm_compute in reify_t2fm (SLNil _)  0 test_4.
  Eval vm_compute in reify_t2fm (SLNil _)  0 test_5.
  Eval vm_compute in reify_t2fm (SLNil _)  0 test_6. *)
End DenoteFM.

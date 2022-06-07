
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

Fixpoint dec_vars (t: term) : term :=
  match t with
  | tRel n => tRel (n - 1)
  | tCast from kind to => 
    tCast (dec_vars from) kind (dec_vars to)
  | tProd na ty body => 
    tProd na (dec_vars ty) (dec_vars body)
  | tLambda na ty body => 
    tLambda na (dec_vars ty) (dec_vars body)
  | tLetIn na def def_ty body =>
    tLetIn na (dec_vars def) (dec_vars def_ty) (dec_vars body)
  | tApp f args => 
    tApp (dec_vars f) (map dec_vars args)
  | tCase ind_nbparams_relevance type_info discr branches =>
    tCase ind_nbparams_relevance (dec_vars type_info) (dec_vars discr) (List.map (fun '(n, t) => (n, dec_vars t)) branches)
  | tProj proj t0 => tProj proj (dec_vars t0)
  | _ => t
  end.

Section ExtractFM.
  Variable (s: signature).
  Variable (m: model s).

  Variable (extract_t2tm : forall c, term -> list (option ({srt & (tm s c srt)})) -> option ({srt & (tm s c srt)})).
  Variable (extract_t2srt : term -> option (sig_sorts s)).

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
          let srt := extract_t2srt pre in 
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
        end
      | _ => None
      end.

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

  Notation res_ty := (option ({ty & s.(mod_sorts) m ty})).
  (* Notation env_ty := ({c & valu s m c}). *)
  Notation env_ty c := (valu s m c).

  Variable (denote_tm : term -> list res_ty -> res_ty).
  Variable (reify_srt : term -> option (s.(sig_sorts))).

  Fixpoint denote_var {c} (env: env_ty c) (n: nat) : res_ty :=
    match env, n with 
    | VSnoc _ _ _ x, 0 => Some (existT _ _ x)
    | VSnoc _ _ env' _, S n' => denote_var env' n'
    | VEmp, _ => None
    end.

  Fixpoint denote_tm' {c} (env: env_ty c) (acc: nat) (t: term) : res_ty :=  
    match t with 
    | tRel n => denote_var env (n - acc)
    | tApp f es => denote_tm t (map (denote_tm' env acc) es)
    | _ => denote_tm t []
    end.

  Obligation Tactic := intros.
  Equations denote_t2fm {c} (env: env_ty c) (anon_acc: nat) (t: term) : Prop by struct t := 
    denote_t2fm env acc t := 
      if eq_term t c_True then True else 
      if eq_term t c_False then False else
      match t with
      | tApp f es => 
        if eq_term f c_eq then 
          match es with 
          | _ :: tl :: tr :: _ => 
            match denote_tm' env acc tl, denote_tm' env acc tr with 
            | Some l, Some r => 
              let (tl, el) := l in 
              let (tr, er) := r in 
                match sorts_eq_dec tl tr with 
                | left HEq => 
                  (el = (eq_rect_r _ er HEq))
                | _ => False
                end
            | _, _ => False
            end
          | _ => False
          end
        else if eq_term f c_or then 
          match es with 
          | tl :: tr :: _ => denote_t2fm env acc tl \/ denote_t2fm env acc tr
          | _ => False
          end
        else if eq_term f c_and then 
          match es with 
          | tl :: tr :: _ => denote_t2fm env acc tl /\ denote_t2fm env acc tr
          | _ => False
          end
        else if eq_term f c_not then 
          match es with 
          | x :: _ => ~ denote_t2fm env acc x
          | _ => False
          end
        else
          False
      | tProd ba_name pre pst => 
        match ba_name.(binder_name) with 
        | nAnon => denote_t2fm env acc pre -> denote_t2fm env (S acc) pst
        | nNamed _ =>
          match reify_srt pre with
          | Some ty' => 
            forall x: (s.(mod_sorts) m ty'), 
              denote_t2fm (VSnoc _ _ ty' c env x) acc pst 
          | None => False
          end
        end
      | _ => False
      end.

  (* MetaCoq Quote Definition test_1 := (False -> True).
  MetaCoq Quote Definition test_2 := (True = False -> False).
  MetaCoq Quote Definition test_3 := (~ ~ False).
  MetaCoq Quote Definition test_4 := (False /\ True).
  MetaCoq Quote Definition test_5 := (forall (x: unit), x = tt).
  MetaCoq Quote Definition test_6 := (forall (x: unit), True \/ False \/ ~ True). *)

  (* Eval vm_compute in denote_t2fm (VEmp _ _)  0 test_1.
  Eval vm_compute in denote_t2fm (VEmp _ _)  0 test_2. 
  Eval vm_compute in denote_t2fm (VEmp _ _)  0 test_3.
  Eval vm_compute in denote_t2fm (VEmp _ _)  0 test_4.
  Eval vm_compute in denote_t2fm (VEmp _ _)  0 test_5.
  Eval vm_compute in denote_t2fm (VEmp _ _)  0 test_6. *)
End DenoteFM.

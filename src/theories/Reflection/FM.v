
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

Fixpoint reindex_vars (t: term) : term :=
  match t with
  | tCast from kind to => 
    tCast (reindex_vars from) kind (reindex_vars to)
  | tProd na ty body => 
    let bod' := reindex_vars body in 
    let bod'' := 
      match na.(binder_name) with 
      | nAnon => dec_vars bod'
      | _ => bod'
      end in
    tProd na (reindex_vars ty) bod''
  | tLambda na ty body => 
    tLambda na (reindex_vars ty) (reindex_vars body)
  | tLetIn na def def_ty body =>
    tLetIn na (reindex_vars def) (reindex_vars def_ty) (reindex_vars body)
  | tApp f args => 
    tApp (reindex_vars f) (map reindex_vars args)
  | tCase ind_nbparams_relevance type_info discr branches =>
    tCase ind_nbparams_relevance (reindex_vars type_info) (reindex_vars discr) (List.map (fun '(n, t) => (n, reindex_vars t)) branches)
  | tProj proj t0 => tProj proj (reindex_vars t0)
  | _ => t
  end.

Section Lenses.
  Variable (s: signature).
  Variable (m: model s).
  Equations mk_var (c: ctx s) (v: valu s m c) (n: nat) : option ({ty & s.(mod_sorts) m ty * var s c ty})%type by struct c := 
    mk_var SLNil _ _ := None;
    (* ugh auto-generated names... *)
    mk_var (Snoc _ srt) (VSnoc _ _ _ x) 0 := Some (v; (x, VHere _ _ _));
    mk_var (Snoc c' ty) (VSnoc _ _ v _) (S n) := 
      (* 
        c' is v1, ty is v0, v is v, n is n
      *)
      match mk_var v1 v n with 
      | Some (ty; (r, v')) => Some (ty; (r, VThere _ _ _ _ v'))
      | None => None
      end.

  (* Parameter dummy_valu : forall (c: ctx s), valu s m c. *)

End Lenses.

Section ExtractFM.
  Variable (s: signature).
  Variable (m: model s).

  Variable (extract_t2tm : forall c, term -> list (option ({srt & (tm s c srt)})) -> option ({srt & (tm s c srt)})).
  Variable (extract_t2srt : term -> option (sig_sorts s)).

  Variable (sort_eq_dec: EquivDec.EqDec (sig_sorts s) eq).

  Equations extract_var (c: ctx s) (n: nat) : option ({srt & var s c srt}) by struct c :=
    extract_var (Snoc _ _ ty) 0 := Some (ty; VHere _ _ ty);
    extract_var (Snoc _ c _) (S n) :=
      match extract_var c n with
      | Some (ty; v') => Some (ty; VThere _ _ _ _ v')
      | None => None
      end;
    extract_var SLNil _ := None.

  Fixpoint extract_t2tm' (c: ctx s) (t: term) : option ({srt & tm s c srt}) :=  
    match t with 
    | tRel n => 
      match extract_var c n with 
      | Some (ty; v) => Some (ty; TVar v)
      | None => None
      end
    | tApp f es => extract_t2tm c t (map (extract_t2tm' c) es)
    | _ => extract_t2tm c t []
    end.

  Obligation Tactic := intros.
  Equations extract_t2fm (c: ctx s) (t: term) : option (fm _ c) by struct t := 
    extract_t2fm c t := 
      if eq_term t c_True then Some FTrue else 
      if eq_term t c_False then Some FFalse else
      match t with
      | tApp f es => 
        if eq_term f c_eq then 
          match es with 
          | _ :: tl :: tr :: _ => 
            match extract_t2tm' c tl, extract_t2tm' c tr with 
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
            match extract_t2fm c tl, extract_t2fm c tr with 
            | Some l, Some r => Some (@FOr _ c l r)
            | _, _ => None
            end
          | _ => None
          end
        else if eq_term f c_and then 
          match es with 
          | tl :: tr :: _ => 
            match extract_t2fm c tl, extract_t2fm c tr with 
            | Some l, Some r => Some (@FAnd _ c l r)
            | _, _ => None
            end
          | _ => None
          end
        else if eq_term f c_not then 
          match es with 
          | x :: _ => 
            match extract_t2fm c x with 
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
          match extract_t2fm c pre, extract_t2fm c pst with 
          | Some el, Some er => Some (FImpl el er)
          | _, _ => None
          end
        | nNamed _ => 
          let srt := extract_t2srt pre in 
          match srt with 
          | Some srt => 
            let c' := Snoc _ c srt in
            let inner := extract_t2fm c' pst in 
            match inner with 
            | Some fm => Some (FForall _ fm)
            | None => None
            end
              
          | None => None
          end
        end
      | _ => None
      end.

  Definition extract_fm t := extract_t2fm (SLNil _) (reindex_vars t).

  (* Some light tests *)
  Variable (c: ctx s).

  MetaCoq Quote Definition test_1 := (False -> True).
  MetaCoq Quote Definition test_2 := (True = False -> False).
  MetaCoq Quote Definition test_3 := (~ ~ False).
  MetaCoq Quote Definition test_4 := (False /\ True).
  MetaCoq Quote Definition test_5 := (forall (x: unit), True -> True).
  MetaCoq Quote Definition test_6 := (forall (x: unit), True \/ False \/ ~ True).

  (* Eval vm_compute in extract_fm test_1.
  Eval vm_compute in extract_fm test_2.
  Eval vm_compute in extract_fm test_3.
  Eval vm_compute in extract_fm test_4.
  Eval vm_compute in extract_fm test_5.
  Eval vm_compute in extract_fm test_6. *)
  
End ExtractFM.
    

Section DenoteFM.

  Variable (s: signature).
  Variable (m: model s).

  Variable (sorts_eq_dec: EquivDec.EqDec (s.(sig_sorts)) eq).

  Notation res_ty := (option ({ty & s.(mod_sorts) m ty})).
  Notation env_ty c := (valu s m c).

  Variable (denote_tm : term -> list res_ty -> res_ty).
  Variable (reify_srt : term -> option (s.(sig_sorts))).

  Fixpoint denote_var {c} (env: env_ty c) (n: nat) : res_ty :=
    match env, n with
    | VSnoc _ _ _ x, 0 => Some (_; x)
    | VSnoc _ _ env' _, S n' => denote_var env' n'
    | VEmp, _ => None
    end.

  Fixpoint denote_tm' {c} (env: env_ty c) (t: term) : res_ty :=  
    match t with 
    | tRel n => 
      match denote_var env n with 
      | Some (ty; r) => Some (ty; r)
      | None => None
      end
    | tApp f es => denote_tm t (map (denote_tm' env) es)
    | _ => denote_tm t []
    end.

  Obligation Tactic := intros.
  Equations denote_t2fm {c} (env: env_ty c) (t: term) : Prop by struct t := 
    denote_t2fm env t := 
      if eq_term t c_True then True else 
      if eq_term t c_False then False else
      match t with
      | tApp f es => 
        if eq_term f c_eq then 
          match es with 
          | _ :: tl :: tr :: _ => 
            match denote_tm' env tl, denote_tm' env tr with 
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
          | tl :: tr :: _ => denote_t2fm env tl \/ denote_t2fm env tr
          | _ => False
          end
        else if eq_term f c_and then 
          match es with 
          | tl :: tr :: _ => denote_t2fm env tl /\ denote_t2fm env tr
          | _ => False
          end
        else if eq_term f c_not then 
          match es with 
          | x :: _ => ~ denote_t2fm env x
          | _ => False
          end
        else
          False
      | tProd ba_name pre pst => 
        match ba_name.(binder_name) with 
        | nAnon => denote_t2fm env pre -> denote_t2fm env pst
        | nNamed _ =>
          match reify_srt pre with
          | Some ty' => 
            forall x: (s.(mod_sorts) m ty'), 
              denote_t2fm (VSnoc _ _ ty' c env x) pst 
          | None => False
          end
        end
      | _ => False
      end.

  Definition denote_fm t := denote_t2fm (VEmp _ _) (reindex_vars t).

  (* Eval vm_compute in denote_fm test_1.
  Eval vm_compute in denote_fm test_2.
  Eval vm_compute in denote_fm test_3.
  Eval vm_compute in denote_fm test_4.
  Eval vm_compute in denote_fm test_5.
  Eval vm_compute in denote_fm test_6. *)
End DenoteFM.

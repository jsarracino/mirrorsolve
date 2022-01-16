From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.

Require Import MirrorSolve.FirstOrder.
Require Import MirrorSolve.HLists.

Import ListNotations.
Import HListNotations.

Require Import Coq.ZArith.BinInt.

Require Import MirrorSolve.N.
Require Import MirrorSolve.Z.

Require Import MirrorSolve.SMT.

Set Universe Polymorphism. 

Section N2Z.

  Definition n2z_sort (ns: N.sorts) : Z.sorts := 
    match ns with 
    | NS => ZS
    | N.BS => BS
    end.

  Fixpoint n2z_arr (na: arity N.sorts) : arity Z.sorts :=
    match na with 
    | nil => nil
    | ns :: na' => n2z_sort ns :: (n2z_arr na')
    end.

  Equations n2z_fun {arr : arity (sig_sorts N.sig)} {srt: sig_sorts N.sig} (nf: sig_funs N.sig arr srt) : sig_funs sig (n2z_arr arr) (n2z_sort srt) :=
  {
    n2z_fun (NLit n) := ZLit (Z.of_nat n);
    n2z_fun (N.BLit b) := BLit b;
    n2z_fun N.Sub := Z.Sub;
    n2z_fun N.Plus := Z.Plus;
    n2z_fun N.Mul := Z.Mul;
    n2z_fun N.Div := Z.Div;
    n2z_fun N.Mod := Z.Mod;
    n2z_fun N.Gt := Z.Gt;
    n2z_fun N.Gte := Z.Gte;
    n2z_fun N.Lt := Z.Lt;
    n2z_fun N.Lte := Z.Lte;
  }.

  Definition n2z_rel {arr: arity (sig_sorts N.sig)} (r: sig_rels N.sig arr) : sig_rels sig (n2z_arr arr) := 
    match r with end.

  Equations n2z_mv {srt} (v: N.mod_sorts srt) : Z.mod_sorts (n2z_sort srt) := 
  {
    @n2z_mv N.NS n := Z.of_nat n;
    @n2z_mv N.BS b := b;
  }.

  

  Program Definition n2z_func : @theory_functor N.sig Z.sig N.fm_model Z.fm_model := {|
    fmap_sorts := n2z_sort;
    fmap_arity := n2z_arr;
    fmap_funs := @n2z_fun;
    fmap_rels := @n2z_rel;
    fmap_mv := @n2z_mv;
  |}.

  (* Notation fmap_ctx := (@fmap_ctx n2z_func). *)

  Notation fmap_ctx' := (fmap_ctx _ _ _ _ n2z_func).

  Equations n2z_fun_arrs {c arr srt} 
    (f: N.funs arr srt) 
    (args: HList.t (fun srt' : N.sorts => FirstOrder.tm sig (fmap_ctx' c) (n2z_sort srt')) arr) : 
    HList.t (FirstOrder.tm sig (fmap_ctx' c)) (n2z_arr arr) := 
  {
    n2z_fun_arrs (NLit n) _ := hnil;
    n2z_fun_arrs (N.BLit b) _ := hnil;
    n2z_fun_arrs N.Sub (x ::: y ::: _) := _;
    n2z_fun_arrs N.Plus (x ::: y ::: _) := _;
    n2z_fun_arrs N.Mul (x ::: y ::: _) := _;
    n2z_fun_arrs N.Div (x ::: y ::: _) := _;
    n2z_fun_arrs N.Mod (x ::: y ::: _) := _;
    n2z_fun_arrs N.Gt (x ::: y ::: _) := _;
    n2z_fun_arrs N.Gte (x ::: y ::: _) := _;
    n2z_fun_arrs N.Lt (x ::: y ::: _) := _;
    n2z_fun_arrs N.Lte (x ::: y ::: _) := _;
  }.
  Next Obligation.
    exact (x ::: y ::: hnil).  (* I don't know why but I can't put this in the body of the definition? *)
  Defined.
  Next Obligation. exact (x ::: y ::: hnil). Defined.
  Next Obligation. exact (x ::: y ::: hnil). Defined.
  Next Obligation. exact (x ::: y ::: hnil). Defined.
  Next Obligation. exact (x ::: y ::: hnil). Defined.
  Next Obligation. exact (x ::: y ::: hnil). Defined.
  Next Obligation. exact (x ::: y ::: hnil). Defined.
  Next Obligation. exact (x ::: y ::: hnil). Defined.
  Next Obligation. exact (x ::: y ::: hnil). Defined.

  Definition n2z_rel_arrs {c arr} (rel: N.rels arr) (args: HList.t (fun srt' : N.sorts => FirstOrder.tm sig (fmap_ctx' c) (n2z_sort srt')) arr) 
    : HList.t (FirstOrder.tm sig (fmap_ctx' c)) (n2z_arr arr) := 
  match rel with end.

  Program Definition n2z_forall_op {c} {srt: sig_sorts N.sig} (f: FirstOrder.fm sig (fmap_ctx' (Snoc _ c srt))) : FirstOrder.fm sig (fmap_ctx' (Snoc _ c srt)) := 
    match srt with 
    | N.BS => f
    | N.NS => 
      FImpl (FEq (s := Z.BS) 
        (TFun _ (@BLit true) hnil) 
        (TFun _ Z.Gte ((TVar (VHere _ _ _)) ::: (TFun _ (@ZLit 0%Z) hnil) ::: hnil))
      ) f
    end.

  Lemma n2z_tm_inj: 
  forall  (srt : sig_sorts N.sig) (c : ctx N.sig) (v : valu N.sig N.fm_model c)
          (t t' : FirstOrder.tm N.sig c srt),
    interp_tm v t = interp_tm v t' <->
    interp_tm (fmap_valu N.sig sig N.fm_model fm_model n2z_func v)
      (fmap_tm N.sig sig N.fm_model fm_model n2z_func (@n2z_fun_arrs) t) =
    interp_tm (fmap_valu N.sig sig N.fm_model fm_model n2z_func v)
      (fmap_tm N.sig sig N.fm_model fm_model n2z_func (@n2z_fun_arrs) t').
  Proof.
    intros.
    dependent induction t using tm_ind';
    dependent destruction t';
    simpl.
    - admit.
    - admit.
    - admit.
    - 
      (* 
      destruct srt. 
      dependent destruction s.
      destruct s eqn:?.
      2: {
        autorewrite with fmap_tm.
        autorewrite with interp_tm.
        simpl.
        autorewrite with n2z_fun.
        autorewrite with mod_fns.
        split; intros; exfalso.
        simple inversion H0.
        inversion_sigma.
        inversion H2.

        dependent H0.

        Set Printing All.
        destruct nat.
        inversion H2.
        inversion H5.
        congruence.
      }
      + split; intros.
        autorewrite with fmap_tm.
        simpl.
        autorewrite with n2z_fun.
        autorewrite with interp_tm in *.
        autorewrite with mod_fns in *.

        inversion s.
        subst args0.
        subst srt.
        destruct t.
        dependent destruction s.
        inversion s.
        inversion t.
        induction s.
        inversion s.
        dependent destruction s.
        dependent induction s.
        
        dependent destruction s.
      inversion s.

      inversion s. *)
  Admitted.

  Lemma n2z_fmap_forall_equi : 
  forall  (srt : sig_sorts N.sig) (c : ctx N.sig) (v : valu N.sig N.fm_model c)
          (f : FirstOrder.fm N.sig (Snoc _ c srt)),
    (forall vA : FirstOrder.mod_sorts N.sig N.fm_model srt,
      interp_fm
        (VSnoc sig fm_model (fmap_sorts n2z_func srt) (fmap_ctx' c)
            (fmap_valu N.sig sig N.fm_model fm_model n2z_func v)
            (fmap_mv n2z_func srt vA))
        (fmap_fm N.sig sig N.fm_model fm_model n2z_func 
            (@n2z_fun_arrs) (@n2z_rel_arrs) (@n2z_forall_op) f)) <->
    (forall vB : FirstOrder.mod_sorts sig fm_model (fmap_sorts n2z_func srt),
      interp_fm
        (VSnoc sig fm_model (fmap_sorts n2z_func srt) (fmap_ctx' c)
            (fmap_valu N.sig sig N.fm_model fm_model n2z_func v) vB)
        (n2z_forall_op
            (fmap_fm N.sig sig N.fm_model fm_model n2z_func 
              (@n2z_fun_arrs) (@n2z_rel_arrs) (@n2z_forall_op) f))).
  Proof.
    intros.
  Admitted.

  Program Definition n2z_wf : functor_wf _ _ _ _ n2z_func (@n2z_fun_arrs) (@n2z_rel_arrs) (@n2z_forall_op) := {|
    interp_tm_inj := n2z_tm_inj;
    fmap_rel_equi := ltac:(intros; inversion r);
    interp_fmap_forall_equi := n2z_fmap_forall_equi;
  |}.

  Lemma n2z_corr: 
    forall (c : ctx N.sig) (v : valu N.sig N.fm_model c) (f : FirstOrder.fm N.sig c),
      interp_fm v f <->
      interp_fm (fmap_valu N.sig sig N.fm_model fm_model n2z_func v)
        (fmap_fm N.sig sig N.fm_model fm_model n2z_func 
            (@n2z_fun_arrs) (@n2z_rel_arrs) (@n2z_forall_op) f).
  Proof.
    eapply fmap_corr.
    exact n2z_wf.
  Qed.

End N2Z.

Require Import Coq.Strings.String.
Require Import MirrorSolve.SMT.

Require Import MirrorSolve.FirstOrder.

Section SMTSig.
  Set Universe Polymorphism.
  Variable (sig: signature).

  Inductive packed_sfun := 
  | PSF: forall args r, sig.(sig_funs) args r -> packed_sfun
  | PSR : forall args, sig.(sig_sorts) -> sig.(sig_rels) args -> packed_sfun
  | PSL : forall X args r, 
    (forall (x: X), sig.(sig_funs) args r) -> 
    packed_sfun.

  Record smt_sig := MkSMTSig {
    sorts : list (sig.(sig_sorts) * smt_sort) ;
    funs : list (packed_sfun * smt_fun) ;
  }.
End SMTSig.

Register MkSMTSig as ms.smt.mk_smt_sig.
Register PSF as ms.smt.psf.
Register PSR as ms.smt.psr.
Register PSL as ms.smt.psl.
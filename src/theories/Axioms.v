Require Import MirrorSolve.FirstOrder.

Require Import MirrorSolve.HLists.

Module UnsoundAxioms.

  Polymorphic Axiom (interp_true: 
    forall s m (form: fm s SLNil), 
      interp_fm (m := m) (VEmp _ _) form
  ).

  Polymorphic Axiom (interp_false: 
    forall s m (form: fm s SLNil), 
      ~interp_fm (m := m) (VEmp _ _) form
  ).

End UnsoundAxioms.
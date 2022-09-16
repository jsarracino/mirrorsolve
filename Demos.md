# Introduction

MirrorSolve's proof automation reflects first-order Coq goals into first-order logic and then discharges the goal using off-the-shelf SMT solvers. 

The reflection is as follows:
* Coq Prop is mapped to SMT bool.
* Coq inductives (that do not have type indices) that live in Type are mapped to equivalent SMT inductive types. So for example, the Coq inductive `Inductive Int_list := | il_nil | il_cons : Z -> Int_list -> Int_list.` is mapped to an equivalent SMT inductive type.
* Coq's Z and bool types are mapped to SMT Z and bool.
* Coq parameter types (e.g. `Variable (A: Type)`) are mapped to SMT uninterpreted sorts.
* Coq functions are mapped to SMT uninterpreted functions.
* Coq inductives that live in Prop are mapped to SMT uninterpreted functions and the constructors are ignored.
* Coq relations that have reasonable SMT interpretations are mapped to their corresponding SMT definitions. In particular we reflect `forall` quantifiers, `/\`, `\/`, `->`, `=`, and `~` to SMT operators. See `src/theories/FirstOrder.v:fm` for our logical AST. 

For a concrete example of proofs using MirrorSolve, see [tests/ListsAuto.v](tests/ListsAuto.v).

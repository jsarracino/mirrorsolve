# Coq proof automation through SMT solvers, reflection and metaprogramming

MirrorSolve is a Coq plugin and library for SMT-powered Coq proof automation. 
It enables:
   * verified compilation of domain-specific verification conditions to SMTLib and using an off-the-shelve solver to discharge the VCs (see [leapfrog](https://github.com/verified-network-toolchain/leapfrog) and [BV.v](src/theories/BV.v));
   * reflecting a library into SMT and using SMT solvers to directly discharge Coq goals (see the Groups portion of [Demos.md](Demos.md));
   * reflecting a library into first-order terms, and then applying further Gallina tranformations to reach an SMTLib theory (see the Nats portion of [Demos.md](Demos.md)).

It currently does not directly translate inductive types, or perform proof reconstruction (so you have to trust the SMT solver output), but those are on the docket for future developments.

# Prerequisites

MirrorSolve requires `dune` and is tested against the dependencies in [dune-project](dune-project) (in particular Coq 8.13, MetaCoq, SMTCoq, and Equations). It also requires one of CVC4, CVC5, Z3, or Boolector to be installed and available as a binary. 

## Building and installing
To build, run: `dune build`. To install, run: `dune install`. If you're using MirrorSolve in another project, you will need to keep track of the output of `dune install` and make sure that other projects include the install directory. 
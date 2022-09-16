# Coq proof automation through SMT solvers, reflection and metaprogramming

MirrorSolve is a Coq plugin and library for SMT-powered Coq proof automation. 
It enables:
   * verified compilation of domain-specific verification conditions to SMTLib and using an off-the-shelve solver to discharge the VCs (see [leapfrog](https://github.com/verified-network-toolchain/leapfrog) and [BV.v](src/theories/BV.v));
   * reflecting a library into SMTLib and using SMT solvers to directly discharge Coq goals (see [Demos.md](Demos.md)).
It currently does not perform proof reconstruction (so you have to trust the SMT solver output),
but it does translate Coq goals to a structured AST for first-order logic,
and we provide a proof of soundness for this translation.

# Prerequisites

MirrorSolve requires `dune` and is tested against the dependencies in [dune-project](dune-project) (in particular Coq 8.15, MetaCoq, SMTCoq, and Equations). It also requires one of CVC4, CVC5, or Z3 to be installed and available as a binary. 

## Building and installing
To build, run: `dune build`. To install, run: `dune install`. If you're using MirrorSolve in another project, you will need to keep track of the output of `dune install` and make sure that other projects include the install directory. 
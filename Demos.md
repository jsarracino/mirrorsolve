# Introduction

The core representation of FOL formula is found in [src/theories/FirstOrder.v](src/theories/FirstOrder.v). The key idea is to parameterize formulas by a *signature* (sorts, function symbols, and relation symbols over the sorts). Another feature of the representation is the use of dependent indices to ensure that variable lookups are well-formed and well-typed. 

## Syntax 
We define three main inductive types:
  * de Bruijn variables, `var`, which are indexed by a surrounding variable context (`ctx`) and a sort for the variable.  
  * FOL terms (`tm`), which are either a variable or a function application from the signature. This type is indexed by a variable context (`ctx`) and a type for the term.
  * FOL formula (`fm`), which are composed of the standard logical operators (conjunction, disjunction, etc), as well as signature relations, and variable quantification. These formula all live in Prop and so are only indexed by a variable context (again `ctx`).

## Semantics
The interpretation of terms/formulas (the `interp_fm` function) is parameterized by an interpretation of the underlying signature. The term interpretation (`interp_tm`) looks up de Bruijn variables within the environment and delegates function symbols to the semantics of the signature.

While the syntax and semantics of FOL terms are a bit mysterious, they are best explained by example. Next we consider two uses of FOL terms to handle Coq goals.
The general formula is to first define a FOL signature, and then make use of MirrorSolve's metaprogramming to reflect and discharge Coq Props.

One caveat: before running the following code, make sure that you have built and installed MirrorSolve using `dune build` and `dune install`. 
 
# Groups
Our first example is drawn from abstract algebra, specifically group theory. 
For the inspiration for this example, please see Arjun Guha's [interesting assignment here](https://people.cs.umass.edu/~arjun/courses/cs691pl-spring2014/assignments/groups.html) (which is itself inspired by Adam Chlipala's book on Certified Programming with Dependent Types, CPDT).

Group theory studies a group G, equipped with:
  1. an identity element `e`;
  2. an inverse operator `inv`;
  3. a binary operator `op`. 

Groups also come equipped with three axioms:
  1. the operator is associative, i.e. `forall a b c, op (op a b) c = op a (op b c)`.
  2. `e` is a right-identity with respect to the operator, i.e. `forall x, op x e = x`.
  3. `inv x` is a right-inverse for `x`, i.e. `forall x, op x (inv x) = e`.

We model these straightforwardly in Coq using parameters and axioms in [tests/Groups.v](tests/Groups.v), lines 9-30. We also solve several group theory examples from Arjun's assignment using plain Ltac (through line 160). 
While these proofs are not terribly difficult,
it turns out that modern SMT solvers can straightforwardly discharge all of these goals,
and we will develop an SMT theory using MirrorSolve that will automatically handle all of them.

## Groups in FOL
The first step is to model groups in FOL, in [src/theories/Groups.v](src/theories/Groups.v). 
The definition is pretty bare (no function or relation symbols); 
the most significant development is an inductive type `sorts` with a single constructor `G'` for the sort of G.

In fact, we will model all three of the group elements (`e`, `inv`, and `op`) as uninterpreted functions. So for now, we return to the (other) groups file, [tests/Groups.v](tests/Groups.v).

## Uninterpreted functions
For uninterpreted functions, the end-user specifies a list of string symbols, as well as their intended interpretation as Coq terms. This interpretation is necessary for MirrorSolve's reflective machinery to convert from normal Coq goals into an equivalent FOL term.

To set this up, we define symbols on lines 182-186 (`symbs`) and their interpretation on lines 188-255. The interpretation is very rote and could potentially be automated away in the future, but fortunately does not take much thought.

## Reflective frontend (Prop -> FOL) 

Next we configure MirrorSolve's reflective automation. On lines 266-280, we create matching functions for terms and sorts (called `match_tacs` and `match_inds` respectively). This machinery operates over the `term` AST defined by the MetaCoq project, which represents Coq's surface syntax as an inductive type `term`. 

MirrorSolve's tactic interpreter (defined in [src/theories/Reflection/Tactics.v](src/theories/Reflection/Tactics.v)) interprets the definition of `match_tacs` to generate two partial functions:
  1. denote, for interpreting from `terms` to a corresponding Coq value;
  2. extract, for converting a `term` into a corresponding FOL term or formula. This translation also handles sorts (thus the definition of `match_inds`). 

In order to make use of the tactic interpreter, we provide a soundness theorem for the generated denote and extract functions, termed `denote_extract_specialized`, which in plain English says that if the extract function produces a FOL formula `fm` from a term `t`, then the denotation of `t` is logically equivalent to the FOL interpretation of the formula `fm`. 

This soundness proof relies on a well-formedness specification for the end-user tactics, in this case `mt_wf`, which boils down to two proofs that the partial functions for denote and extract have equivalent behavior. This well-formedness spec should be solved by to-be-developed automation in the future, so for the moment, we leave it admitted (rest assured that it is true for this example).

## SMT backend

Finally on lines 313-317 we configure the SMT backend, by adding a custom SMT sort for G, 
as well as uninterpreted function symbols for `e`, `inv`, and `op`. 

## Final proof

Finally we will discharge a proof (namely `unique_id`) using MirrorSolve. First, we quote the proof into a MetaCoq term using MetaCoq's definition on lines 328-333. Notice that the group axioms are encoded using quantified arms of an implication.
Next, we start an alternate proof of `unique_id`, `unique_id'` on lines 335-340.

We will use two proof steps;
  1. translate to a corresponding FOL formula using MirrorSolve's tactics. This is done by calling the `reflect_goal` tactic with a bunch of problem specific arguments (in this case, a bunch of information about the UF+Groups theory, as well as the particular MetaCoq term for dual reflection and extraction). After this tactic, the new goal is now an interpretation of a corresponding FOL formula.
  2. discharge the FOL term to an off-the-shelf SMT solver and trust the result. This is done in a type-safe way (vs using `admit`) by the `check_interp_pos` tactic and the `interp_true` axiom. In this case, `check_interp_pos G` is a primitive exposed by the OCaml plugin portion of MirrorSolve. It behaves like `idtac` if the goal `G` is checked by a solver to SAT, and otherwise fails.
  There is a corresponding `check_interp_neg` for checking whether a goals is UNSAT or not.

# Nats
  
Another interesting (and useful) SMT theory is an automated theory for Coq `nats`. 
For this example, defined in [tests/Nats.v](tests/Nats.v), we use MirrorSolve to discharge a tricky lemma useful for proving the irrationality of sqrt(2).

This property, which is `lem_0` in [CoqHammer's examples](https://github.com/lukaszcz/coqhammer/blob/coq8.15/examples/sqrt2_irrational.v), is the following: 

```Coq
forall n m: nat, 
  n <> 0 -> 
  m * m = 2 * n * n -> 
  Nat.ltb m (2 * n) = true
```

MirrorSolve includes theories for [natural numbers](src/theories/N.v) and [integers](src/theories/Z.v), as well as a [conversion functor between them called N2Z](src/theories/N2Z.v). We will make use of all three of these theories (notice that nats do not have a corresponding SMTLib theory, so we do the standard trick of translating to Z).

## Reflection configuration
Similar to the groups example, we again generate denotation and extraction functions using match tactics on lines 33-44. A slight wrinkle is that we also generate denote/extract for constants (the `natLit` and `boolLit` notations). 

## Backend configuration
We also configure the SMT backend to map MirrorSolve's Z theory to corresponding portions of SMTLib's Z theory, on lines 65-72.

## Proof
The final proof, on line 86, again starts by reflecting the goal to a corresponding FOL formula.
However, at this point, the FOL formula is in the theory of N. 
To convert to a proper SMTLib theory, Z, we use the N2Z functor;
in particular, the `n2z_corr` lemma translates the formula.

Finally, we compute the translation functions induced by `n2z_corr` (which constrain quantified Z variables to be strictly nonnegative and map between function symbols), and again discharge to SMT.


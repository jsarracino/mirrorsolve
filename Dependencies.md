# Opam instructions

You can find opam [here](https://opam.ocaml.org/doc/Install.html) and the documentation [here](https://opam.ocaml.org/doc/FAQ.html).
We'll be making a new switch, adding some extra Coq repositories to the switch, and pinning Coq to 8.18.0.

## Making the switch
Run the following command to make a new switch (named coq.8.18):

```console
opam switch create coq.8.18 --packages=ocaml-variants.5.1.1+options,ocaml-option-flambda
eval $(opam env --switch=coq.8.18)
```

You might need to run `opam init` if this is your first opam switch.

Once the switch is built, run the following to add Coq 8.18.0 and pin its version:

```console
opam install coq.8.18.0
opam pin coq 8.18.0
```

## Adding extra repos

We need several extra repos:

```console
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
```

# Dependency instructions

We use the [dune](https://dune.build) build tool. A handy feature of dune is that it will generate the opam dependencies for a project.

First get dune through opam:

```console
opam install dune
```

Next you can run the following to add the dependencies:

```console
dune build
    # (this will fail, with a message complaining about Equations, but crucially it builds mirrorsolve.opam)
opam install --deps-only .
```

And after this finishes, `dune build` should properly work!
# FreeSpec

FreeSpec is a framework for implementing, certifying, and executing
impure computations in Coq.

## Overview

This repository contains three Coq packages:

- `coq-freespec-core` provides the foundation of the FreeSpec formalism.
- `coq-freespec-exec` provides the means to execute impure
  computations implemented with the help of `coq-freespec-core`.
- `coq-freespec-stdlib` provides a small “impure effects” library to
  write impure computations more easily.

The codebase is organized as follows:

- The Coq definitions of the three theories live in the `theories/`
  directory.
- The OCaml source of the Coq plugins live in the `plugins/` directory.
- There are examples for the three plugins in the `examples/` directory.

## Getting Started

FreeSpec depends on [`coqffi`](https://github.com/coq-community/coqffi).

```bash
dune build
dune install
```

Besides, we provide two helper scripts:

- `run-tests.sh` executes each Coq file living in `tests/` and reports
  any error
- `build-docs.sh` builds the OCaml and Coq source documentation

Said documentations are published
[here](https://ANSSI-FR.github.io/FreeSpec).

In addition, FreeSpec has been the subject of two academic
publications.

- [**FreeSpec: Specifying, Certifying and Executing Impure Computations
  in Coq**](https://hal.inria.fr/hal-02422273) (CPP'20)
- [**Modular Verification of Programs with Effects and Effect Handlers in
  Coq**](https://hal.inria.fr/hal-01799712) (FM'18)

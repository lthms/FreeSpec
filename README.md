# FreeSpec

FreeSpec is a framework for the Coq proof assistant to modularly verify programs
with effects and effect handlers. It relies on the Program monad as defined in
the [`operational` package](https://hackage.haskell.org/package/operational) of
Haskell, and uses so-called abstract specifications to specify, for each effect,
expected properties for the effect result, independently of any underlying
effect handler.

## Overview

This repository can be divided into several parts:

* `theories/Control` defines a Monad typeclasses hierarchy, and will eventually
  get its own repository
* `theories/` defines the core formalism of FreeSpec, it is “the framework” per
  se
* `examples/` implements a complete example which involves the most important
  aspects of FreeSpec

In addition to these mature parts, there are other sub-projects in this
repository:

* `specs/` is an ongoing effort to provide generic construction to model
  hardware components, including a type to work with fixed-size integers, an
  indexed Monad to parse bit fields, etc.
* `poc/` is an ongoing experiment to specify and verify a web service with
  FreeSpec

## Getting Started

FreeSpec has been tested with Coq v8.7, and should work with Coq v8.6. To build
the proofs, just use the Makefile at the root of the project:

```bash
make
```

To explore the project, you can build the HTML documentation (`make html`). The
most important modules are covered.

## About the Project

FreeSpec has been described in an academic paper submitted to the Formal Methods
2018 conference. If you are interested, do not hesitate to [ask for the
paper](mailto:thomas.letan@ssi.gouv.fr).

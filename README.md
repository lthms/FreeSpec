# FreeSpec

FreeSpec is a framework for the Coq proof assistant to modularly verify programs
with effects and effect handlers. It relies on the Program monad as defined in
the operational package of Haskell, and uses so-called abstract specifications
to specify, for each effect, expected properties for the effect result,
independently of any underlying effect handler.

FreeSpec has been tested with Coq v8.7, and should work with Coq v8.6. To build
the proofs, just use the Makefile at the root of the project:

```bash
make
```

FreeSpec has been described in an academic paper submitted to the Formal Methods
2018 conference. The terminology used in the project is different than the one
used in the paper, and will be revise promptly.

The two main differences are:

* **Operational semantics** (paper) versus **Interpreters** (code).
* **Abstract Specifications** (paper) versus **Contracts** (code).

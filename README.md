# FreeSpec

## Getting Started

```bash
git clone git@gitlab.inria.fr:freespec/freespec freespec
cd freespec
git submodule init && git submodule update
make
```

## Extraction

The Extraction is currently setup to use the
[`haskell-extraction` plugin](https://github.com/RafaelBocquet/haskell-extraction)
developed by [Rafaël Bocquet](https://github.com/RafaelBocquet).

Once FreeSpec has been compiled (`make`), a file `OUT.coc` should be present at
the root of the project. To be able to turn it into an Haskell file, you need to
use the `haskell-of-coq` tool provided by `haskell-extraction`.

```bash
cd libs/haskell-extraction/haskell
stack build
stack exec haskell-of-coq -- ../../../OUT.coc
```

The result is both printed in stdout and in a file called `OUT.hs`.

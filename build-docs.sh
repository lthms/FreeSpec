#!/bin/bash

set -e

dune build
chmod -R +w _build/
coq_makefile -f _CoqProject -o Makefile
make html mlihtml
mkdir -p docs/
rm -rf docs/coq docs/ml
mv html docs/coq
mv mlihtml docs/ml
dune clean

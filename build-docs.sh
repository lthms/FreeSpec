#!/bin/bash

# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

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

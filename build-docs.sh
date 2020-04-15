#!/bin/bash

set -e

./configure.sh
make html
make mlihtml
mkdir -p docs/
rm -rf docs/coq docs/ml
mv html docs/coq
mv mlihtml docs/ml

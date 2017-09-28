Require Import FreeSpec.Specs.x86.

Extraction Language Haskell.

Require Import ExtrHaskell.
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.
Require Import ExtrHaskellString.

Require Import FreeSpec.Control.IO.ExtrHaskell.

Cd "specs/x86/x86-hs/src".
Separate Extraction x86Main.
Cd "../../../..".
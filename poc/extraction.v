Require Import FreeSpec.PoC.CoqMain.
Require Import FreeSpec.Control.IO.ExtrHaskell.

Extraction Language Haskell.

Require Import ExtrHaskell.
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.
Require Import ExtrHaskellString.

Extract Constant putStrLn => "Prelude.putStrLn".

Cd "poc/poc-hs/src".
Separate Extraction CoqMain.
Cd "../../..".
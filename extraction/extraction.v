Require Import FreeSpec.Interface.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Program.
Require Import FreeSpec.Oracle.Oracle.

Require Import FreeSpec.Examples.Map.

Add LoadPath "./libs/haskell-extraction/ocaml/".

Require Import HaskellExtraction.HaskellExtraction.

Extraction Language Haskell.

Extraction "FreeSpec"
           Program.Program Program.runProgram'
           Map.IMap test_interpreter.
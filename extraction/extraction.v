Require Import FreeSpec.Interface.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Program.
Require Import FreeSpec.Oracle.Oracle.

Require Import FreeSpec.Examples.Map.
Require Import FreeSpec.Specs.Memory.

(** * Haskell Extraction Plugin
 *)
Add LoadPath "./libs/haskell-extraction/ocaml/".

Require Import HaskellExtraction.HaskellExtraction.

Hextraction , Map.IMap.

(** * Ocaml Regular Extraction

 *)

Extraction Language Haskell.

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.

Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

Extraction "FreeSpec"
           Program.runProgram' Memory.mem
           Control.Identity.Identity Control.Identity.identity_Monad
           Memory.append Map.IMap test_interpreter.
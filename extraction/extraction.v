Require Import FreeSpec.Interface.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Program.
Require Import FreeSpec.Oracle.Oracle.

Require Import FreeSpec.Control.Option.
Require Import FreeSpec.Examples.Map.
Require Import FreeSpec.Specs.Memory.
Require Import FreeSpec.Specs.x86.MCH.MCH.

Extraction Language Haskell.

(* TODO: this does not work:
> Set Extraction Conservative Types.

   Coq output:
> File "./extraction/extraction.v", line 31, characters 0-184:
> Anomaly:
> File "plugins/extraction/extraction.ml", line 824, characters 3-9: Assertion failed.
> Please report at http://coq.inria.fr/bugs/.
 *)

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.

Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

Cd "extraction/hs".
Separate Extraction FreeSpec.MonadSemantics FreeSpec.Specs.x86.MCH.MCH
         FreeSpec.Control.Option.
Cd "../..".
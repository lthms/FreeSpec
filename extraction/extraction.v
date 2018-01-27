(* FreeSpec
 * Copyright (C) 2018 ANSSI
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>.
 *)

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
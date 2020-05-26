(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2018–2019 Thomas Letan <thomas.letan@ssi.gouv.fr>
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

From FreeSpec.Core Require Import Core.

Axioms (i1 i2 i3 i4 : interface).

Axiom p1 : forall `{Provide ix}, impure ix nat.
Axiom p2 : forall `{Provide2 ix i3 i1}, impure ix nat.

Definition p `{Provide4 ix i1 i4 i3 i2} : impure ix nat :=
  p1;;
  p2.

Definition provide_notation_test_1 {a} `{StrictProvide3 ix i1 i2 i3} (p : i2 a) : ix a :=
  inj_p p.

Lemma provide_notation_test_2 `{StrictProvide3 ix i1 i2 i3} : StrictProvide2 ix i2 i3.

Proof.
  typeclasses eauto.
Qed.

Definition provide_notation_test_3 {a} (i1 i2 i3 : interface) (p : i2 a) : (iplus (iplus i1 i2) i3) a :=
  inj_p p.

Lemma provide_notation_test_4 (i1 i2 i3 : interface) : Provide (i1 + (i2 + i3)) i2.

Proof.
  typeclasses eauto.
Qed.

Lemma provide_notation_test_5 (i1 i2 i3 : interface) : StrictProvide2 (i1 + i2 + i3) i2 i1.

Proof.
  typeclasses eauto.
Qed.

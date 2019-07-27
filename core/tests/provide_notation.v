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

From FreeSpec.Core Require Import Impure.

#[local]
Definition provide_notation_test_1 {a}
  (ix i1 i2 i3 : interface) `{ix :| i1, i2, i3} (p : i2 a) : ix a :=
  lift_eff p.

Definition provide_notation_test_2 {a} (ix i1 i2 i3 : interface) `{ix :| i1, i2, i3}
  (p : forall i' `{ix :| i2, i3}, i' a)
  : ix a :=
  p ix.

Definition provide_notation_test_3 {a} (i1 i2 i3 : interface) (p : i2 a)
  : (i1 ⊕ i2 ⊕ i3) a :=
  lift_eff p.

Lemma provide_notation_test_4 (i1 i2 i3 : interface)
  : i1 ⊕ (i2 ⊕ i3) :| i2.
Proof.
  typeclasses eauto.
Qed.

Lemma provide_notation_test_5 (i1 i2 i3 : interface)
  : i1 ⊕ i2 ⊕ i3 :| i2, i1.
Proof.
  typeclasses eauto.
Qed.

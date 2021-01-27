(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

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

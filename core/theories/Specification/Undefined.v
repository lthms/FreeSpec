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

Require Import FreeSpec.Undefined.
Require Import FreeSpec.Specification.
Require Import FreeSpec.Semantics.

(** We now define a generic-purpose specification called “escape the
    undefined hell”. From a safety/secure point of view, one should
    avoid the [undef] instruction at all cost, because we cannot
    reason about it.

    The [escape_undefined_hell] is here to verify that.

 *)
Definition escape_undefined_hell_step :=
  fun (R:  Type)
      (_:  Undefined R)
      (_:  R)
      (_:  unit)
  => tt.

Definition escape_undefined_hell_precondition :=
  fun (R:  Type)
      (_:  Undefined R)
      (_:  unit)
  => False.

Definition escape_undefined_hell_postcondition :=
  fun (R:  Type)
      (_:  Undefined R)
      (_:  R)
      (_:  unit)
  => True.

Definition escape_undefined_hell
  : Specification unit Undefined :=
  {| abstract_step  := escape_undefined_hell_step
   ; precondition   := escape_undefined_hell_precondition
   ; postcondition  := escape_undefined_hell_postcondition
   |}.

(** It is easy to prove that any [Semantics Undefined] [i] complies to
    with specification if the counter is still set to [0], that is: [i
    :> escape_undefined_hell [tt]]

 *)

Lemma escape_undefined_hell_compliance
      (int:  Sem.t Undefined)
  : int |= escape_undefined_hell [tt].
Proof.
  constructor.
  + intros A e Hpre.
    destruct Hpre.
  + intros A e Hpre.
    destruct Hpre.
Qed.

(** The main idea behing the [escape_undefined_hell] specification is
    to be used as soon as the [Undefined] interface is used in a
    model.

 *)
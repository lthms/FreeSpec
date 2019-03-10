(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2019 Thomas Letan <thomas.letan@ssi.gouv.fr>
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

Require Import FreeSpec.Program.

Require Import Prelude.Control.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Local Open Scope prelude_scope.

Class HasExecIsomorphism (A: Type).

Instance bool_ExecIso: HasExecIsomorphism bool.
Instance Z_ExecIso: HasExecIsomorphism Z.
Instance ascii_ExecIso: HasExecIsomorphism ascii.
Instance string_ExecIso: HasExecIsomorphism string.

Module Debug.
  Inductive i: Type -> Type :=
  | Inspect: forall {A} `{HasExecIsomorphism A}, A -> i unit.

  Definition inspect {ix} `{Use i ix} {A} `{HasExecIsomorphism A}
    : A -> Program ix unit :=
    request <<< Inspect.
End Debug.

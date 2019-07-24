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

From FreeSpec Require Import Core.

From Coq Require Import BinNums Ascii String.

Generalizable All Variables.

Class HasExecIsomorphism (a : Type).

Instance bool_ExecIso : HasExecIsomorphism bool.
Instance Z_ExecIso : HasExecIsomorphism Z.
Instance ascii_ExecIso : HasExecIsomorphism ascii.
Instance string_ExecIso : HasExecIsomorphism string.

Inductive DEBUG : interface :=
(** Should acts as [id] as long as there is no bug in the FreeSpec.Exec plugin
    (primilarly intended to write test cases for conversion functions in Coq) *)
| Iso `{HasExecIsomorphism a} : a -> DEBUG a

(** Get a string which describes the argument (from the Exec plugin
    perspective). *)
| Inspect `{HasExecIsomorphism a} : a -> DEBUG string.

Definition inspect `{HasExecIsomorphism a, ix :| DEBUG} (x : a) : impure ix string :=
  request (Inspect x).

Definition iso `{HasExecIsomorphism a, ix :| DEBUG} (x : a) : impure ix a :=
  request (Iso x).

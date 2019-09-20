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

From Coq Require Import BinNums Ascii String.
From FreeSpec Require Import Core.

Generalizable All Variables.

(** * Disclaimer

   This library is mostly intended to provide facilities to test
   <<FreeSpec.Exec>>, and shall not be used in production code. *)

(** * <<Exec>> Isomorphisms *)

(** One of the key action of <<FreeSpec.Exec>> is to provide “translation
    helpers” to turn a Coq term into an OCaml value and vice versa.  It is
    expected that these functions form isomorphisms; meaning that
    <<from_ocaml(from_coq(t)) = t>> and <<from_coq(from_ocaml(v)) = v>>.

    <<FreeSpec.Exec>> users can obviously define there own translation
    functions, but the plugin defines several base functions; the concerned
    types are provided an instance for the dummy typeclass [HasExecIsomorphism].
    The typeclass is used to constrain the arguments of the [DEBUG] interface
    primitives. As long as <<FreeSpec.Exec>> does not provide a way to extend
    this interface implementation, _you shall not provide instances of_
    [HasExecIsomorphism] _for your own types_.
 *)

Class HasExecIsomorphism (a : Type) := {}.

Instance bool_ExecIso : HasExecIsomorphism bool := {}.
Instance Z_ExecIso : HasExecIsomorphism Z := {}.
Instance ascii_ExecIso : HasExecIsomorphism ascii := {}.
Instance string_ExecIso : HasExecIsomorphism string := {}.

(** * The [DEBUG] Interface *)

(** The main objective of the [DEBUG] interface is to provide primitives to
    debug and test <<FreeSpec.Exec>> translation functions. *)

Inductive DEBUG : interface :=

(** The [Iso] primitive, on the one hand, should acts as [id] as long as there
    is no bug in the FreeSpec.Exec plugin (primilarly intended to write test
    cases for conversion functions in Coq) *)

| Iso `{HasExecIsomorphism a} : a -> DEBUG a

(** The [Inspect] primitive, on the other hand, should compute a string which
    describes its argument (from the Exec plugin perspective). *)

| Inspect `{HasExecIsomorphism a} : a -> DEBUG string.

(** As mentionned in the [FreeSpec.Exec] library, due to recent changes in
    <<Coq-8.10>>, you now need to register interfaces types and constructors to
    the kernel in order for <<FreeSpec.Exec>> to be able to recognize them. *)

Register DEBUG as freespec.exec.debug.type.
Register Iso as freespec.exec.debug.Iso.
Register Inspect as freespec.exec.debug.Inspect.

Definition inspect `{HasExecIsomorphism a, Provide ix DEBUG} (x : a) : impure ix string :=
  request (Inspect x).

Definition iso `{HasExecIsomorphism a, Provide ix DEBUG} (x : a) : impure ix a :=
  request (Iso x).

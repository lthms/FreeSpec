(* FreeSpec
 * Copyright (C) 2018–2020 ANSSI
 *
 * Contributors:
 * 2020 Thomas Letan <thomas.letan@ssi.gouv.fr>
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

From FreeSpec.Core Require Import Core Extraction.
From FreeSpec.FFI Require Import FFI Refs.
From FreeSpec.Exec Require Import Exec.

From Coq Require Import String.

Open Scope nat_scope.

Definition with_heap `{Monad m, MonadRefs m} : m string :=
  let* ptr := make_ref 2 in
  assign ptr 3;;
  let* x := deref ptr in
  if Nat.eqb x 2
  then pure "yes!"
  else pure "no!".

(* Coq projects the [with_heap] polymorphic definition directly into [impure],
   thanks to its typeclass inference algorithm. *)
Definition with_heap_impure `{Provide ix REFS} : impure ix string :=
  with_heap.

Exec with_heap_impure.

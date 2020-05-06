(* FreeSpec
 * Copyright (C) 2018–2020 ANSSI
 *
 * Contributors:
 * 2018–2020 Thomas Letan <thomas.letan@ssi.gouv.fr>
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

From FreeSpec.Core Require Import All.

(** We provide an interface to manipulate so-called references, analogous to the
    ['a ref] type of OCaml.

    We first introduce the [ref] type, as an axiom. We do that in order to
    ensure that a user of this interface cannot create or modify of type
    [ref]. *)

Axiom ref : Type -> Type.

(** The only way to manipulate a reference shall be the [HEAP] interface, which
    provides the means to: *)

Inductive HEAP : interface :=

(**   - Create a new reference with a given initial value. *)

| NewRef {a} : a -> HEAP (ref a)

(**   - Destruct a reference, which is analogous the the [free] function in
        C. Using this primitive may not be mandatory. It dependes on how the
        program which uses this interface is executed. If the program is
        extracted to OCaml, and then compiled, the garbage collector will handle
        this task just fine. On the contrary, when executed with the [Exec]
        command, not calling [Destruct] leads to memory leaks. *)

| Destruct {a} : ref a -> HEAP unit

(**   - Change the content assigned to a given reference. *)

| Assign {a} : ref a -> a -> HEAP unit

(**   - Fetch the content assigned to a given reference. *)

| Deref {a} : ref a -> HEAP a.

Arguments NewRef [a] _.
Arguments Destruct [a] _.
Arguments Assign [a] _ _.
Arguments Deref [a] _.

Register HEAP as freespec.exec.heap.type.
Register NewRef as freespec.exec.heap.NewRef.
Register Destruct as freespec.exec.heap.Destruct.
Register Assign as freespec.exec.heap.Assign.
Register Deref as freespec.exec.heap.Deref.

Definition new_ref `{Provide ix HEAP} {a} (init : a) : impure ix (ref a) :=
  request (NewRef init).

Definition destruct `{Provide ix HEAP} {a} (p : ref a) : impure ix unit :=
  request (Destruct p).

Definition assign `{Provide ix HEAP} {a} (p : ref a) (x : a) : impure ix unit :=
  request (Assign p x).

Definition deref `{Provide ix HEAP} {a} (p : ref a) : impure ix a :=
  request (Deref p).

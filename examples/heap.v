(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

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

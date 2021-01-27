(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(* Coq Set-up *)

Generalizable All Variables.

(** * Coq Stdlib Notations *)

From Coq Require Export List RelationClasses Setoid Morphisms.
Import ListNotations.

Open Scope signature_scope.
Close Scope nat_scope.
Open Scope bool_scope.

From ExtLib Require Import Functor Applicative Monad.
Import FunctorNotation.
Import ApplicativeNotation.
Import MonadLetNotation.

Open Scope monad_scope.

From ExtLib Require Import Extras.
Import FunNotation.

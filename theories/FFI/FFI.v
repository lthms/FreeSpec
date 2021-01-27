(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From FreeSpec Require Import Core Extraction.
From CoqFFI Require Import Interface.

Instance FreeSpec_Inject `(H : Provide ix i) : Inject i (impure ix) :=
  { inject := @request ix i _ H }.

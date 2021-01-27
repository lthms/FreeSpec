(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From FreeSpec Require Import Core.

Inductive EVAL (a : Type) : Type :=
| Eval (x : a) : EVAL a.

Arguments Eval [a] (x).

Definition eval `{Provide ix EVAL} {a} (x : a) : impure ix a :=
  request (Eval x).

Register EVAL as freespec.exec.eval.type.
Register Eval as freespec.exec.eval.Eval.

(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2021 Nomadic Labs *)

From FreeSpec.Core Require Import Core.
From FreeSpec.FFI Require Import FFI.
From CoqFFI Require Import Interface.

Class MonadRaise (α : Type) (m : Type -> Type) :=
  { raise {β} : α -> m β }.

Arguments raise [α m MonadRaise β] _.

Inductive RAISE (α : Type) : interface :=
| Raise {β} : α -> RAISE α β.

Arguments Raise [α β] _.

Definition inj_raise `{Inject (RAISE α) m} (β : Type) (x : α) : m β :=
  inject (Raise x).

Instance inj_Raise `{Inject (RAISE α) m} : MonadRaise α m :=
  { raise := inj_raise }.

Fixpoint with_abort `(p : impure (ix + RAISE β) α)
  : impure ix (α + β) :=
  match p with
  | request_then (in_right (Raise x)) _ => local (inr x)
  | request_then (in_left p) k => request_then p (fun x => with_abort (k x))
  | local x => local (inl x)
  end.

Definition try_or `{Monad m, Inject (RAISE α) m} `(p : m (β + α))
  : m β :=
  let* x := p in
  match x with
  | inl x => ret x
  | inr err => raise err
  end.
     

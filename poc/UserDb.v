(* FreeSpec
 * Copyright (C) 2018 ANSSI
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

Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Option.
Require Import FreeSpec.PoC.Db.
Require Import FreeSpec.Program.
Require Import FreeSpec.WEq.

Require Import Coq.Strings.String.

Local Open Scope free_weq_scope.

Inductive TransportError
  : Type :=
| transport_error.

Record User :=
  { email:   string
  ; name:    string
  ; token:   option string
  }.

Module UserDbSpec <:  DbSpec.
  Definition K   := nat.
  Definition Res := User.
  Definition Err := TransportError.
End UserDbSpec.

Module Export UserDb := DB UserDbSpec.

Definition head
           {A:  Type}
           (l:  list A)
  : option A :=
  match l with
  | cons x rest
    => Some x
  | nil
    => None
  end.

Definition user_from_email
           (ml:  string)
  : Program Query (option UserDb.Entity) :=
  head <$> DSL.select (fun entity
                       => ml ?= email (val entity)).

Definition user_key_from_email
           (ml:  string)
  : Program Query (option nat) :=
  map key <$> user_from_email ml.
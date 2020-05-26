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

From Base Require Import Prelude.
From FreeSpec.Core Require Import All.
From FreeSpec.Stdlib Require Import Env.

Inductive ARGS : interface :=
| ArgCount : ARGS i63
| ArgValue (nth : i63) : ARGS (option bytestring).

Definition arg_count `{Provide ix ARGS} : impure ix i63 := request ArgCount.

Definition arg_value `{Provide ix ARGS} (nth : i63) : impure ix (option bytestring) :=
  request (ArgValue nth).

#[local]
Definition args `{Provide ix ENV} : component ARGS ix :=
  fun (α : Type) (e : ARGS α) =>
    match e in ARGS α return impure ix α with
    | ArgCount => let* x := getenv "FREESPEC_EXEC_ARGC" in
                  match x >>= int_of_bytestring with
                  | Some x => pure x
                  | None => pure 0%i63
                  end
    | ArgValue n => getenv ("FREESPEC_EXEC_ARGV_" ++ (bytestring_of_int n))
    end.

Definition with_args {a} `{Provide ix ENV} : impure (ix + ARGS) a -> impure ix a :=
  with_component (pure tt) args (pure tt).

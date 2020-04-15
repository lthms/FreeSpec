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

From Coq Require Export Int63.
From Prelude Require Import Int Text Bytes.
From FreeSpec.Stdlib Require Import Env.

Inductive ARGS : interface :=
| ArgCount : ARGS int
| ArgValue (nth : int) : ARGS bytes.

Definition arg_count `{Provide ix ARGS} : impure ix int := request ArgCount.

Definition arg_value `{Provide ix ARGS} (nth : int) : impure ix bytes := request (ArgValue nth).

#[local]
Definition args `{Provide ix ENV} : component ARGS ix :=
  fun* (a : Type) (e : ARGS a) =>
    match e with
    | ArgCount => do let* x := get_env (bytes_of_text t#"FREESPEC_EXEC_ARGC") in
                     match text_of_bytes x >>= int_of_text with
                     | Some x => pure x
                     | None => pure 0%int63
                     end
                  end
    | ArgValue n => get_env (bytes_of_text (t#"FREESPEC_EXEC_ARGV_" ++ (text_of_int n)))
    end.

Definition with_args {a} `{Provide ix ENV} : impure (ix + ARGS) a -> impure ix a :=
  with_component (pure tt) args (pure tt).

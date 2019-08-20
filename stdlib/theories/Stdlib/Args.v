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

From Coq Require Import ZArith String.
From FreeSpec Require Import Exec.
From FreeSpec.Stdlib Require Import Env.
From Prelude Require Import Z.

Generalizable All Variables.

Inductive ARGS : interface :=
| ArgCount : ARGS Z
| ArgValue (nth : Z) : ARGS string.

Definition arg_count `{ix :| ARGS} : impure ix Z :=
  request ArgCount.

Definition arg_value `{ix :| ARGS} (nth : Z) : impure ix string :=
  request (ArgValue nth).

#[local]
Definition args `{ix :| ENV} : component ARGS ix unit :=
  fun (a : Type) (e : ARGS a) =>
    match e with
    | ArgCount => Z_of_string <$> lift (get_env "FREESPEC_EXEC_ARGC")
    | ArgValue n => lift (get_env (append "FREESPEC_EXEC_ARGV_" (string_of_Z n)))
    end.

Definition with_args {a} `{ix :| ENV} : impure (ARGS ⊕ ix) a -> impure ix a :=
  with_component (pure tt) args (fun _ => pure tt).

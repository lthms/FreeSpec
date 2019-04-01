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

Require Export Coq.Strings.String.

Require Import Prelude.Control.

Require Import FreeSpec.Exec.
Require Import FreeSpec.Program.

#[local]
Open Scope prelude_scope.

Module Env.
  Inductive i: Type -> Type :=
  | GetVar: string -> i string
  | SetVar: string -> string -> i unit.

  Definition get
             {ix} `{Use i ix}
    : string -> Program ix string :=
    request <<< GetVar.

  Definition set
             {ix} `{Use i ix}
             (var: string)
    : string -> Program ix unit :=
    request <<< (SetVar var).
End Env.

Declare ML Module "stdlib_env_plugin".
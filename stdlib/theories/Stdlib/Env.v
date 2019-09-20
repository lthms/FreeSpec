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

From Coq Require Import String.
From FreeSpec Require Export Exec.

#[local]
Open Scope string_scope.

Generalizable All Variables.

Inductive ENV : interface :=
| GetEnv (name : string) : ENV string
| SetEnv (name : string) (value : string) : ENV unit.

Register ENV as freespec.stdlib.env.type.
Register GetEnv as freespec.stdlib.env.GetEnv.
Register SetEnv as freespec.stdlib.env.SetEnv.

Definition get_env `{Provide ix ENV} (name : string) : impure ix string :=
  request (GetEnv name).

Definition set_env `{Provide ix ENV} (name : string) (value : string) : impure ix unit :=
    request (SetEnv name value).

Declare ML Module "freespec_stdlib_env".

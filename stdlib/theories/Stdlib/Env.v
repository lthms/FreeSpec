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

From Prelude Require Export Bytes.
From FreeSpec Require Export Exec.

Generalizable All Variables.

Inductive ENV : interface :=
| GetEnv (name : bytes) : ENV bytes
| SetEnv (name : bytes) (value : bytes) : ENV unit.

Register ENV as freespec.stdlib.env.type.
Register GetEnv as freespec.stdlib.env.GetEnv.
Register SetEnv as freespec.stdlib.env.SetEnv.

Definition get_env `{Provide ix ENV} (name : bytes) : impure ix bytes :=
  request (GetEnv name).

Definition set_env `{Provide ix ENV} (name : bytes) (value : bytes) : impure ix unit :=
  request (SetEnv name value).

Declare ML Module "freespec_stdlib_env".

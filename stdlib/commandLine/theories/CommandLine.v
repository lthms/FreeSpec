(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2019 Vincent Tourneur <vincent.tourneur@inria.fr>
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

Require Import FreeSpec.Exec.
Require Export Coq.Strings.String.
Require Import FreeSpec.Program.
Require Import BinInt.

Module CommandLine.
  Inductive i: Type -> Type :=
  | Argc: i Z
  | Arg: Z -> i string.

  Definition argc {ix} `{Use i ix}
    : Program ix Z :=
    request Argc.

  Definition arg {ix} `{Use i ix} (n: Z)
    : Program ix string :=
    request (Arg n).
End CommandLine.

Declare ML Module "stdlib_commandLine_plugin".

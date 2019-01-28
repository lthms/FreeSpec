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

Require Import Coq.Strings.String.
Require Import FreeSpec.Program.
Require Import FreeSpec.Compose.

Module Console.
  Inductive i: Type -> Type :=
  | Scan: i string
  | Echo: string -> i unit.

  Definition scan {ix} `{Use i ix}
    : Program ix string :=
    request Scan.

  Definition echo {ix} `{Use i ix} (str: string)
    : Program ix unit :=
    request (Echo str).
End Console.

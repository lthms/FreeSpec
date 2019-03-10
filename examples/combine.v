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
Require Import FreeSpec.Exec.
Require Import FreeSpec.Stdlib.Console.
Require Import FreeSpec.Program.
Require Import Prelude.Control.

Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.

Local Open Scope prelude_scope.

Definition combine {ix} `{Use Console.i ix} `{Use Debug.i ix}: Program ix unit :=
  Debug.iso 10 >>= Debug.inspect >>= Console.echo ;;
  Debug.iso true >>= Debug.inspect >>= Console.echo.

(* for Console.i <+> Debug.i *)
Exec combine.

Axiom (ix: Type -> Type).
Axiom (Use_console_ix: Use Console.i ix).
Axiom (Use_debug_ix: Use Debug.i ix).

(* for the most generic form *)
Exec (@combine ix Use_console_ix Use_debug_ix).

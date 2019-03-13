#!/usr/bin/env fsrun

(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * Vincent Tourneur <vincent.tourneur@inria.fr>
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

Require Import FreeSpec.Stdlib.Console.
Require Import FreeSpec.Stdlib.CommandLine.
Require Import FreeSpec.Program.
Require Import Prelude.Control.
Require Import BinInt.
Require Import String.
Require Import Ascii.

Local Open Scope prelude_scope.

Definition new_line := String "010"%char EmptyString.

Fixpoint print_args_aux {ix} `{Use Console.i ix} `{Use CommandLine.i ix} (t: Z) (n: nat) : Program ix unit :=
  match n with
  | S m => CommandLine.arg (t - ((Z.of_nat m) + 1)) >>= Console.echo;; Console.echo " ";; print_args_aux t m
  | _ => Console.echo new_line
  end.
Definition print_args {ix} `{Use Console.i ix} `{Use CommandLine.i ix} (n: Z) := print_args_aux n (Z.to_nat n).

Definition main {ix} `{Use Console.i ix} `{Use CommandLine.i ix} :=
  CommandLine.argc >>= print_args.

(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
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

Require Import Coq.Program.Wf.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import FreeSpec.Exec.Interfaces.
Require Import FreeSpec.Exec.Plugin.
Require Import FreeSpec.Program.
Require Import FreeSpec.Compose.
Require Import Prelude.Control.

Local Open Scope prelude_scope.
Local Open Scope char_scope.
Require Import PeanoNat.

Definition ascii_of_nat n :=
  match n mod 10 with
  | 0 =>  "0"
  | 1 =>  "1"
  | 2 =>  "2"
  | 3 =>  "3"
  | 4 =>  "4"
  | 5 =>  "5"
  | 6 =>  "6"
  | 7 =>  "7"
  | 8 =>  "8"
  | _ =>  "9"
  end.

Program Fixpoint string_of_nat_aux acc n {measure n} :=
  match n with
  | 0 => acc
  | _ => string_of_nat_aux (String (ascii_of_nat (n mod 10)) acc)
                           (n / 10)
  end.
Next Obligation.
  fold (Nat.div n 10).
  apply Nat.div_lt.
  apply Nat.neq_0_lt_0.
  intro F.
  now symmetry in F.
  repeat constructor.
Defined.

Definition string_of_nat := string_of_nat_aux "".

Definition nat_of_string (s: string) : nat :=
  let fix aux acc s :=
      match s with
      | String "0" rst => aux (10 * acc) rst
      | String "1" rst => aux (1 + 10 * acc) rst
      | String "2" rst => aux (2 + 10 * acc) rst
      | String "3" rst => aux (3 + 10 * acc) rst
      | String "4" rst => aux (4 + 10 * acc) rst
      | String "5" rst => aux (5 + 10 * acc) rst
      | String "6" rst => aux (6 + 10 * acc) rst
      | String "7" rst => aux (7 + 10 * acc) rst
      | String "8" rst => aux (8 + 10 * acc) rst
      | String "9" rst => aux (9 + 10 * acc) rst
      | _ => acc
      end
  in aux 0 s.

Fixpoint fibonacci n :=
  match n with
  | O => 1
  | 1 => 1
  | S m => match m with
           | O => 1
           | 1 => 1
           | S r => fibonacci r
           end + fibonacci m
  end.


Definition fibo {ix} `{Use Console.i ix} : Program ix unit :=
  Console.echo "Go! ";;
  x <- Console.scan;
  let res := fibonacci (nat_of_string x) in
  Console.echo (string_of_nat res).

Exec fibo.
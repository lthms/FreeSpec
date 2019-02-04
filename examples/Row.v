(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2018–2019 Thomas Letan <thomas.letan@ssi.gouv.fr>
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

Require Import Coq.Lists.List.

Require Import FreeSpec.Interface.
Require Import FreeSpec.Program.
Require Import FreeSpec.Specification.
Require Import FreeSpec.Compose.
Require Import FreeSpec.Semantics.

Require Import FreeSpec.Experiment.Row.

Require Import Prelude.Control.

Local Open Scope prelude_scope.
Local Open Scope free_row_scope.

Inductive NatStack
  : Type -> Type :=
| Push (x: nat)
  : NatStack unit
| Pop
  : NatStack nat.

Definition push_nat
           {eff:  list (Type -> Type)} `{HasEffect eff NatStack}
           (x:    nat)
  : Program (row eff) unit :=
  request (Push x).

Definition pop_nat
           {eff:  list (Type -> Type)} `{HasEffect eff NatStack}
  : Program (row eff) nat :=
  request Pop.

Inductive LogNat
  : Type -> Type :=
| Log (x:  nat)
  : LogNat unit.

Definition log_nat
           {eff:  list (Type -> Type)} `{HasEffect eff LogNat}
           (n:    nat)
  : Program (row eff) unit :=
  request (Log n).

Definition my_program
           {eff:  list (Type -> Type)} `{HasEffect eff NatStack}
           `{HasEffect eff LogNat}
           (x:    nat)
  : Program (row eff) unit :=
  y <- pop_nat;
    push_nat x;;
             log_nat y.

Definition stack_sem
  : Sem.t NatStack :=
  mkSemantics (fun (A:  Type)
                   (l:  list nat)
                   (e:  NatStack A)
               => match e with
                  | Push x
                    => (tt, x :: l)
                  | Pop
                    => match l with
                       | x :: r
                         => (x, r)
                       | _
                         => (0, nil)
                       end
                  end) nil.

Definition log_sem
  : Sem.t LogNat :=
  mkSemantics (fun (A:  Type)
                   (l:  list nat)
                   (e:  LogNat A)
               => match e with
                  | Log x
                    => (tt, x :: l)
                  end) nil.

Definition example_semantics :=
  <<| stack_sem; log_sem |>>.

Definition test :=
  evalProgram example_semantics (my_program 0).

Goal (test = tt).
  reflexivity.
Qed.

Definition spec_stack
  : Specification nat NatStack :=
  {| abstract_step  := fun (a:  Type)
                           (e:  NatStack a)
                           (x:  a)
                           (s:  nat)
                       => S s
  ; precondition   := no_pre
  ; postcondition  := fun (a:  Type)
                          (e:  NatStack a)
                          (x:  a)
                          (s:  nat)
                      => True
  |}.

Definition spec_log
  : Specification nat LogNat :=
  {| abstract_step  := fun (a:  Type)
                           (e:  LogNat a)
                           (x:  a)
                           (s:  nat)
                       => S s
  ; precondition   := no_pre
  ; postcondition  := fun (a:  Type)
                          (e:  LogNat a)
                          (x:  a)
                          (s:  nat)
                      => True
  |}.

Definition example_specification :=
  |< spec_stack; spec_log >|.

Definition full_stack :=
  specification_derive (my_program 0)
                       <<| stack_sem; log_sem |>>
                       |< spec_stack; spec_log >|
                       << 0; 0 >>.

Goal (full_stack = << 2; 1>>).
  reflexivity.
Qed.
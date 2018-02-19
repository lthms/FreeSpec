Require Import FreeSpec.Interface.
Require Import FreeSpec.Control.
Require Import FreeSpec.Program.
Require Import FreeSpec.Specification.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Row.
Require Import Coq.Lists.List.

Local Open Scope free_control_scope.
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
  inj_effect (Push x).

Definition pop_nat
           {eff:  list (Type -> Type)} `{HasEffect eff NatStack}
  : Program (row eff) nat :=
  inj_effect Pop.

Inductive LogNat
  : Type -> Type :=
| Log (x:  nat)
  : LogNat unit.

Definition log_nat
           {eff:  list (Type -> Type)} `{HasEffect eff LogNat}
           (n:    nat)
  : Program (row eff) unit :=
  inj_effect (Log n).

Definition my_program
           {eff:  list (Type -> Type)} `{HasEffect eff NatStack}
           `{HasEffect eff LogNat}
           (x:    nat)
  : Program (row eff) unit :=
  y <- pop_nat;
    push_nat x;;
             log_nat y.

Definition stack_sem
  : Semantics NatStack :=
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
  : Semantics LogNat :=
  mkSemantics (fun (A:  Type)
                   (l:  list nat)
                   (e:  LogNat A)
               => match e with
                  | Log x
                    => (tt, x :: l)
                  end) nil.

Definition example_semantics :=
  <| stack_sem; log_sem |>.

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
                       <| stack_sem; log_sem |>
                       |< spec_stack; spec_log >|
                       << 0; 0 >>.

Goal (full_stack = << 2; 1>>).
  reflexivity.
Qed.
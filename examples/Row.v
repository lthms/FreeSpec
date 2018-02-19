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
  remember (runProgram example_semantics pop_nat).
  cbn in Heqp.
  unfold push_sem in Heqp;
    unfold sem_nil in Heqp.
  reflexivity.
Qed.

Axioms (spec_stack:  Specification nat NatStack)
       (spec_log:    Specification nat LogNat).

Definition example_specification :=
  |< spec_stack; spec_log >|.
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

Require Import Coq.Program.Equality.

Require Import Prelude.Control.
Require Import Prelude.Control.Classes.
Require Import Prelude.Tactics.

Require Import FreeSpec.Tactics.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Program.
Require Import FreeSpec.Compose.
Require Import FreeSpec.Component.
Require Import FreeSpec.Specification.

Local Open Scope prelude_scope.
Local Open Scope free_scope.

(** The objective of the present document is to give an example of the
    FreeSpec methodology. The object of study is a simple airlock
    controller that controls two doors. The system to model and verify is depicted in the following
    figure:

    #<img src="controller.svg" style="display: block; margin:auto;"/>#

    The traditional security policy targeted by a airlock system is to
    prevent both doors to be open at the same time. This example is
    interesting because it is subject to the so-called _temporary
    violation problem_ (see Example 6.1 of this #<a
    href="https://lthms.xyz/docs/manuscript.pdf">#PhD manuscript#</a>#
    if you are not familiar with this challenge). We therefore
    demonstrate how FreeSpec can be used in order to prevent such
    pitfall. *)

(** * Controller Interface *)

Inductive door := In | Out.

Definition co (d: door): door :=
  match d with In => Out | Out => In end.

Module controller.
  Inductive i: Interface :=
  | Tick: i unit
  | OpenDoor: door -> i unit.

  Definition tick {Ix} `{Use i Ix}: Program Ix unit :=
    request Tick.

  Definition open_door {Ix} `{Use i Ix}: door -> Program Ix unit :=
    request <<< OpenDoor.
End controller.

(** * Door Interface *)

Module door.
  Inductive i {L} (l: L): Interface :=
  | IsOpen: i l bool
  | Toggle: i l unit.

  Arguments IsOpen {L l}.
  Arguments Toggle {L l}.

  Definition is_open {L Ix} (l: L) `{Use (i l) Ix}: Program Ix bool :=
    request IsOpen.

  Definition toggle {L Ix} (l: L) `{Use (i l) Ix}: Program Ix unit :=
    request Toggle.
End door.

#[program]
Instance use_door
         (l: door)
  : Use (door.i l) (door.i In <+> door.i Out) :=
  { lift_eff :=  match l with
                 | In => fun _ op => InL op
                 | Out => fun _ op => InR op
                 end
  }.

(** * Controller Model *)

Definition open_door {L Ix} (l: L) `{Use (door.i l) Ix}: Program Ix unit :=
  d <- door.is_open l;
  when (negb d) $ door.toggle l.

Definition close_door {L Ix} (l: L) `{Use (door.i l) Ix}: Program Ix unit :=
  d <- door.is_open l;
  when d $ door.toggle l.

Definition controller: Component controller.i nat (door.i In <+> door.i Out) :=
  fun _ op =>
    match op with
    | controller.Tick
      => c <- get;
         if Nat.ltb c 15
         then lift (close_door In);;
              lift (close_door Out);;
              put 0
         else put (S c)
    | controller.OpenDoor l
      => lift (close_door (co l));;
         lift (open_door l);;
         put 0
    end.

(** * Controller Verification *)

(** ** Abstract Step Function *)

Definition doors_abs_step {A}
           (op:  (door.i In <+> door.i Out) A)
           (x:   A)
           (b:   bool * bool)
  : bool * bool :=
  match op with
  | InL door.Toggle => (negb (fst b), snd b)
  | InR door.Toggle => (fst b, negb (snd b))
  | _  => b
  end.

(** ** Precondition *)

Inductive doors_pre
  : forall {A}, (door.i In <+> door.i Out) A -> (bool * bool) -> Prop :=
(* ------------------------------------------------------------ *)
(** To open the inside door ([i = false]), the outside door needs to
    be closed ([o = false]). *)
| doors_pre_toggle_in
    (i o:  bool)
    (Ho:   i = false -> o = false)
  : doors_pre (InL door.Toggle) (i, o)
(* ------------------------------------------------------------ *)
(** To open the outside door ([o = false]), the inside door needs to
    be closed ([i = false]). *)
| doors_pre_toggle_out
    (i o:  bool)
    (Ho:   o = false -> i = false)
  : doors_pre (InR door.Toggle) (i, o)
(* ------------------------------------------------------------ *)
(** It is always allowed to request the state of the inside door. *)
| doors_pre_is_open_in
    (i o:  bool)
  : doors_pre (InL door.IsOpen) (i, o)
(* ------------------------------------------------------------ *)
(** It is always allowed to request the state of the outside door. *)
| doors_pre_is_open_out
    (i o:  bool)
  : doors_pre (InR door.IsOpen) (i, o).

(** ** Postcondition *)

Inductive doors_post
  : forall {A}, (door.i In <+> door.i Out) A -> A -> (bool * bool) -> Prop :=
(* ------------------------------------------------------------ *)
(** No expectation as [door.Toggle] does not return meaningful results
 *)
| doors_post_toggle_in
    (i o:  bool)
  : doors_post (InL door.Toggle) tt (i, o)
(* ------------------------------------------------------------ *)
(** No expectation as [door.Toggle] does not return meaningful results
 *)
| doors_post_toggle_out
    (i o:  bool)
  : doors_post (InR door.Toggle) tt (i, o)
(* ------------------------------------------------------------ *)
(** The inside door state is expected not to have changed since the
    last time we have toggled it *)
| doors_is_open_in
    (i o:  bool)
  : doors_post (InL door.IsOpen) i  (i, o)
(* ------------------------------------------------------------ *)
(** The outside door state is expected not to have changed since the
    last time we have toggled it *)
| doors_is_open_out
    (i o:  bool)
  : doors_post (InR door.IsOpen) o  (i, o).

(** ** The Abstract Specification *)

Definition doors_specs: Specification (bool * bool) (door.i In <+> door.i Out) :=
  {| abstract_step := @doors_abs_step
  ;  precondition := @doors_pre
  ;  postcondition := @doors_post
  |}.

(** * Proof of Correctness *)

(** It is expected that our airlock system is _safe_, independently
    from how it is being used by its environment. Therefore, the
    statement to prove does not mention any abstract specification for
    [controller.i].

    We leverage the [prove_program] defined by FreeSpec to explore the
    different control flow pathes of the [controller] programs, and
    the only goals to prove are related to precondition compliance. *)

Lemma close_door_is_correct
      (b:   bool * bool)
      (l:   door)
  : close_door l |> doors_specs [b].
Proof.
  induction l;
    prove_program.
  + induction b;
      constructor.
  + inversion Hpost; ssubst.
    constructor.
    now intro F.
  + induction b;
      constructor.
  + inversion Hpost; ssubst.
    constructor.
    now intro F.
Qed.

Definition get_state
           (d: door)
  : bool * bool -> bool :=
  match d with
  | In => fst
  | Out => snd
  end.

Ltac sinversion H := inversion H; try ssubst.

Lemma close_door_specs
      (b w:  bool * bool)
      (l:    door)
      (r:    unit)
  : correct_run doors_specs b (close_door l) r w
    -> get_state l w = false.
Proof.
  intros H.
  induction l;
    induction b;
    sinversion H;
    induction x;
    sinversion Hx;
    sinversion Hf;
    try sinversion Hf0;
    reflexivity.
Qed.

Lemma open_door_is_correct
      (b:   bool * bool)
      (l:   door)
  : get_state (co l) b = false -> open_door l |> doors_specs [b].
Proof.
  intro H.
  destruct b.
  induction l; cbn in H; subst;
    prove_program; now (constructor + auto).
Qed.

#[local] Opaque open_door.
#[local] Opaque close_door.

Lemma controller_is_correct
      (b:   bool * bool)
      (c:   nat)
  : forall {A} (op: controller.i A),
    controller A op c |> doors_specs[b].
Proof.
  intros A op.
  induction op;
    prove_program.
  + apply close_door_is_correct.
  + apply close_door_is_correct.
  + apply close_door_is_correct.
  + apply open_door_is_correct.
    eapply close_door_specs.
    exact Hrun.
Qed.
(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2021 Nomadic Labs *)

From FreeSpec.Core Require Import Core CoreFacts.
From FreeSpec.Contribs Require Import Raise MFix MFixFacts.

Inductive PICK : interface :=
| Pick (x : nat) : PICK unit.

Definition pick `{Provide ix PICK} (x : nat) : impure ix unit :=
  request (Pick x).

Module const_call.
  (* Our goal is to prove that [forever_pick x] only calls [Pick x]
     and nothing else. *)
  Definition forever_pick `{Provide2 ix PICK MFIX} (x : nat)
    : impure ix False :=
    mfix (fun rec x => pick x ;; rec x) x.

  Inductive pick_caller_obligation (x : nat)
    : unit -> forall (a : Type), PICK a -> Prop :=
  | pick_caller : pick_caller_obligation x tt unit (Pick x).

  Hint Constructors pick_caller_obligation : loop.

  Definition pick_me (x : nat) : contract PICK unit :=
    {| witness_update := fun _ _ _ _ => tt
     ; caller_obligation := pick_caller_obligation x
     ; callee_obligation := no_callee_obligation
    |}.

  Lemma forever_trustworthy `{StrictProvide3 ix PICK MFIX (RAISE nat)} (x : nat)
    : pre (to_hoare (ix:=ix) (pick_me x) (forever_pick x)) tt.

  Proof.
    apply mfix_pre.
    induction gas.
    + prove impure.
    + prove impure with loop.
  Qed.
End const_call.

Module inc_call.
  (* This time, we prove [forever_pick x] first calles [Pick x], then
     [Pick (x+1)], and so forth. *)
  Definition forever_pick `{Provide2 ix PICK MFIX} (x : nat)
    : impure ix False :=
    mfix (fun rec x => pick x ;; rec (x + 1)%nat) x.

  Inductive pick_caller_obligation (x : nat)
    : forall (a : Type), PICK a -> Prop :=
  | pick_caller : pick_caller_obligation x unit (Pick x).

  Hint Constructors pick_caller_obligation : loop.

  Definition pick_me : contract PICK nat :=
    {| witness_update := fun x _ _ _ => (x+1)%nat
     ; caller_obligation := pick_caller_obligation
     ; callee_obligation := no_callee_obligation
    |}.

  Lemma forever_trustworthy `{StrictProvide3 ix PICK MFIX (RAISE nat)} (x : nat)
    : pre (to_hoare (ix:=ix) pick_me (forever_pick x)) x.

  Proof.
    apply mfix_pre.
    intros gas.
    revert x.
    induction gas; intros x.
    + prove impure.
    + prove impure with loop.
  Qed.
End inc_call.

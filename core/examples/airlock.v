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

From Coq Require Import Arith.
From FreeSpec Require Import Core.

(** * Specifying

    ** Doors *)

Inductive door : Type := left | right.

Inductive DOORS : interface :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

Definition is_open {ix} `{ix :| DOORS} (d : door) : program ix bool :=
  request (IsOpen d).

Definition toggle {ix} `{ix :| DOORS} (d : door) : program ix unit :=
  request (Toggle d).

Definition open_door {ix} `{ix :| DOORS} (d : door) : program ix unit :=
  var open ← is_open d in
  when (negb open) (toggle d).

Definition close_door {ix} `{ix :| DOORS} (d : door) : program ix unit :=
  var open ← is_open d in
  when open (toggle d).

(** ** Controller *)

Inductive CONTROLLER : interface :=
| Tick : CONTROLLER unit
| RequestOpen (d : door) : CONTROLLER unit.

Definition tick {ix} `{ix :| CONTROLLER} : program ix unit :=
  request Tick.

Definition request_open {ix} `{ix :| CONTROLLER} (d : door) : program ix unit :=
  request (RequestOpen d).

Definition co (d : door) : door :=
  match d with
  | left => right
  | right => left
  end.

From Prelude Require Import State.

Definition controller : component CONTROLLER DOORS nat :=
  fun _ op =>
    match op with
    | Tick =>
      var cpt ← get in
      when (15 <? cpt) (do
        lift (close_door left);
        lift (close_door right);
        put 0)
    | RequestOpen d => do
        lift (close_door (co d));
        lift (open_door d);
        put 0
    end.

(** * Verifying *)

Definition Ω : Type := bool * bool.

Definition sel (d : door) : Ω -> bool :=
  match d with
  | left => fst
  | right => snd
  end.

Definition tog (d : door) (ω : Ω) : Ω :=
  match d, ω with
  | left, (l, r) => (negb l, r)
  | right, (l, r) => (l, negb r)
  end.

Lemma tog_equ_1 (d : door) (ω : Ω)
  : sel d (tog d ω) = negb (sel d ω).
Proof.
  destruct d; destruct ω; reflexivity.
Qed.

Lemma tog_equ_2 (d : door) (ω : Ω)
  : sel (co d) (tog d ω) = sel (co d) ω.
Proof.
  destruct d; destruct ω; reflexivity.
Qed.

Opaque tog.

Definition step (a : Type) (ω : Ω) (e : DOORS a) (x : a) :=
  match e with
  | Toggle d => tog d ω
  | _ => ω
  end.

Inductive req : forall (a : Type), Ω -> DOORS a -> Prop :=
| req_is_open (d : door) (ω : Ω)
  : req bool ω (IsOpen d)

| req_toggle (ω : Ω) (d : door) (H : sel d ω = false -> sel (co d) ω = false)
  : req unit ω (Toggle d).

Inductive prom: forall (a : Type), Ω -> DOORS a -> a -> Prop :=

| prom_is_open (d : door) (ω : Ω) (x : bool) (equ : sel d ω = x)
  : prom bool ω (IsOpen d) x

| prom_toggle (d : door)(ω : Ω) (x : unit)
  : prom unit ω (Toggle d) x.

Definition doors_specs : specs DOORS Ω :=
  {| witness_update := step
  ; requirements := req
  ; promises := prom
  |}.

From Prelude Require Import Tactics.

Lemma close_door_trustworthy (ω : Ω) (d : door)
  : trustworthy_program doors_specs ω (close_door d).

Proof.
  prove_program; cbn; repeat constructor; subst.
  inversion Hpost; ssubst.
  now rewrite H1.
Qed.

Lemma open_door_trustworthy (ω : Ω) (d : door) (safe : sel (co d) ω = false)
  : trustworthy_program doors_specs ω (open_door d).

Proof.
  prove_program; cbn; repeat constructor; subst.
  inversion Hpost; ssubst.
  now rewrite safe.
Qed.

Definition safe_open_door {ix} `{ix :| DOORS} (d : door) : program ix unit :=
  do close_door (co d);
     open_door d.

Lemma close_door_run (ω : Ω) (d : door) (ω' : Ω) (x : unit)
  (run : trustworthy_run doors_specs (close_door d) ω ω' x)
  : sel d ω' = false.
Proof.
  inversion run; ssubst.
  cbn in *.
  inversion prom0; ssubst.
  case_eq (sel d ω); intros equ; rewrite equ in rec.
  + inversion rec; ssubst.
    cbn in rec0.
    inversion rec0; ssubst.
    rewrite tog_equ_1.
    rewrite equ.
    reflexivity.
  + inversion rec; ssubst.
    exact equ.
Qed.

#[local] Opaque close_door.
#[local] Opaque open_door.

Lemma safe_door_trustworthy (ω : Ω) (d : door)
  : trustworthy_program doors_specs ω (safe_open_door d).

Proof.
  prove_program; cbn; repeat constructor; subst.
  apply close_door_trustworthy.
  apply close_door_run in Hrun.
  apply open_door_trustworthy.
  exact Hrun.
Qed.

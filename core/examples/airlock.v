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

Generalizable All Variables.

Definition is_open `{ix :| DOORS} (d : door) : impure ix bool :=
  request (IsOpen d).

Definition toggle `{ix :| DOORS} (d : door) : impure ix unit :=
  request (Toggle d).

Definition open_door `{ix :| DOORS} (d : door) : impure ix unit :=
  var open ← is_open d in
  when (negb open) (toggle d).

Definition close_door `{ix :| DOORS} (d : door) : impure ix unit :=
  var open ← is_open d in
  when open (toggle d).

(** ** Controller *)

Inductive CONTROLLER : interface :=
| Tick : CONTROLLER unit
| RequestOpen (d : door) : CONTROLLER unit.

Definition tick `{ix :| CONTROLLER} : impure ix unit :=
  request Tick.

Definition request_open `{ix :| CONTROLLER} (d : door) : impure ix unit :=
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
  match d with
  | left => (negb (fst ω), snd ω)
  | right => (fst ω, negb (snd ω))
  end.

Lemma tog_equ_1 (d : door) (ω : Ω)
  : sel d (tog d ω) = negb (sel d ω).
Proof.
  destruct d; reflexivity.
Qed.

Lemma tog_equ_2 (d : door) (ω : Ω)
  : sel (co d) (tog d ω) = sel (co d) ω.
Proof.
  destruct d; reflexivity.
Qed.

Opaque tog.

Definition step (ω : Ω) (a : Type) (e : DOORS a) (x : a) :=
  match e with
  | Toggle d => tog d ω
  | _ => ω
  end.

Inductive req : Ω -> forall (a : Type), DOORS a -> Prop :=
(** Given the door [d] of o system [ω], it is always possible to ask for the
    state of [d]. *)
| req_is_open (d : door) (ω : Ω)
  : req ω bool (IsOpen d)

(** Given the door [d] of o system [ω], if [d] is closed, then the second door
    [co d] has to be closed to for a request to toggle [d] to be valid. *)
| req_toggle (d : door) (ω : Ω) (H : sel d ω = false -> sel (co d) ω = false)
  : req ω unit (Toggle d).

Inductive prom: Ω -> forall (a : Type), DOORS a -> a -> Prop :=

(** When a system in a state [ω] reports the state of the door [d], it shall
    reflect the true state of [d]. *)
| prom_is_open (d : door) (ω : Ω) (x : bool) (equ : sel d ω = x)
  : prom ω bool (IsOpen d) x

(** There is no particular promises on the result [x] of a request for [ω] to
    close the door [d]. *)
| prom_toggle (d : door) (ω : Ω) (x : unit)
  : prom ω unit (Toggle d) x.

Definition doors_specs : specs DOORS Ω := Build_specs _ _ step req prom.

From Prelude Require Import Tactics.

(** Closing a door [d] in any system [ω] is always a trustworthy operation. *)
Lemma close_door_trustworthy (ω : Ω) (d : door)
  : trustworthy_impure doors_specs ω (close_door d).

Proof.
  (* We use the [prove_program] tactics to erease the program monad *)
  prove_impure; cbn; repeat constructor; subst.
  (* This leaves us with one goal to prove:

       [sel d ω = false -> sel (co d) ω = false]

     Yet, thanks to our call to [IsOpen d], we can predict that

       [sel d ω = true] *)
  inversion Hpost; ssubst.
  now rewrite H1.
Qed.

Lemma open_door_trustworthy (ω : Ω) (d : door) (safe : sel (co d) ω = false)
  : trustworthy_impure doors_specs ω (open_door d).

Proof.
  prove_impure; cbn; repeat constructor; subst.
  inversion Hpost; ssubst.
  now rewrite safe.
Qed.

Definition safe_open_door {ix} `{ix :| DOORS} (d : door) : impure ix unit :=
  do close_door (co d);
     open_door d.

Lemma close_door_run (ω : Ω) (d : door) (ω' : Ω) (x : unit)
  (run : trustworthy_run doors_specs (close_door d) ω ω' x)
  : sel d ω' = false.
Proof.
  inversion run; ssubst; clear run req0; cbn in *.
  inversion prom0; ssubst; clear prom0.
  case_eq (sel d ω); intros equ; rewrite equ in rec;
    inversion rec; ssubst; cbn in *; try clear req.
  + inversion rec0; ssubst; clear rec0.
    rewrite tog_equ_1.
    rewrite equ.
    reflexivity.
  + inversion rec; ssubst; clear rec.
    exact equ.
Qed.

#[local] Opaque close_door.
#[local] Opaque open_door.
#[local] Opaque Nat.ltb.

Lemma safe_door_trustworthy (ω : Ω) (d : door)
  : trustworthy_impure doors_specs ω (safe_open_door d).

Proof.
  prove_impure; cbn; repeat constructor; subst.
  apply close_door_trustworthy.
  apply close_door_run in Hrun.
  apply open_door_trustworthy.
  exact Hrun.
Qed.

Lemma trustworthy_run_inv {a} (p : impure DOORS a)
  (ω : Ω) (safe : sel left ω = false \/ sel right ω = false)
  (x : a) (ω' : Ω) (run : trustworthy_run doors_specs p ω ω' x)
  : sel left ω' = false \/ sel right ω' = false.

Proof.
  induction run.
  + exact safe.
  + apply IHrun.
    clear f run IHrun ω' y.
    destruct e;
      inversion prom0; ssubst;
      inversion req0; ssubst; cbn -[sel].
    ++ apply safe.
    ++ destruct safe as [safe | safe]; destruct d.
       +++ (* The left door is closed, we toggle the left door. Because of
              [doors_specs], we know the right door has to be closed. *)
           right.
           fold (co left).
           rewrite tog_equ_2.
           now apply H1.
       +++ (* The left door is closed, we want to toggle the right door. We know
              the left door will remain closed. *)
           left.
           fold (co right).
           rewrite tog_equ_2.
           exact safe.
       +++ (* The right door is closed, we want to toggle the left door. We know
              the right door will remain closed. *)
           right.
           fold (co left).
           rewrite tog_equ_2.
           exact safe.
       +++ (* The right door is closed, we want to toggle the right
              door. Because of [doors_specs], we know the left door has to be
              closed. *)
           left.
           fold (co right).
           rewrite tog_equ_2.
           now apply H1.
Qed.

Lemma controller_correct
  : correct_component controller
                      (no_specs CONTROLLER)
                      doors_specs
                      (fun _ _ d => sel left d = false \/ sel right d = false).
Proof.
  intros ωc cpt ωd pred a e req.
  split.
  + destruct e.
    ++ prove_impure; apply close_door_trustworthy.
    ++ prove_impure.
       apply close_door_trustworthy.
       apply open_door_trustworthy.
       now apply close_door_run in Hrun.
  + intros x st ωj' run.
    split; auto.
    eapply trustworthy_run_inv; [ exact pred
                                |  exact run ].
Qed.

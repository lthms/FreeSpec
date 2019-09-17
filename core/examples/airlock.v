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
From Prelude Require Import Tactics.

(** * Specifying *)

(** ** Doors *)

Inductive door : Type := left | right.

Definition door_eq_dec (d d' : door) : { d = d' } + { ~ d = d' } :=
  ltac:(decide equality).

Inductive DOORS : interface :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

Generalizable All Variables.

Definition is_open `{ix :| DOORS} (d : door) : impure ix bool :=
  request (IsOpen d).

Definition toggle `{ix :| DOORS} (d : door) : impure ix unit :=
  request (Toggle d).

Definition open_door `{ix :| DOORS} (d : door) : impure ix unit :=
  do var open <- is_open d in
     when (negb open) (toggle d)
  end.

Definition close_door `{ix :| DOORS} (d : door) : impure ix unit :=
  do var open <- is_open d in
     when open (toggle d)
   end.

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
      do var cpt <- get in
         when (15 <? cpt) do
           lift (close_door left);
           lift (close_door right);
           put 0
         end
      end
    | RequestOpen d => do
        lift (close_door (co d));
        lift (open_door d);
        put 0
      end
    end.

(** * Verifying the Airlock Controller *)

(** ** Doors Specification *)

(** *** Witness States *)

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

(** From now on, we will reason about [tog] using [tog_equ_1] and [tog_equ_2].
    FreeSpec tactics rely heavily on [cbn] to simplify certain terms, so we use
    the <<simpl never>> options of the [Arguments] vernacular command to prevent
    [cbn] from unfolding [tog].

    This pattern is common in FreeSpec.  Later in this example, we will use this
    trick to prevent [cbn] to unfold impure computations covered by intermediary
    theorems. *)

#[local] Arguments tog : simpl never.

Definition step (ω : Ω) (a : Type) (e : DOORS a) (x : a) :=
  match e with
  | Toggle d => tog d ω
  | _ => ω
  end.

(** *** Requirements *)

Inductive req : Ω -> forall (a : Type), DOORS a -> Prop :=

(** - Given the door [d] of o system [ω], it is always possible to ask for the
      state of [d]. *)

| req_is_open (d : door) (ω : Ω)
  : req ω bool (IsOpen d)

(** - Given the door [d] of o system [ω], if [d] is closed, then the second door
      [co d] has to be closed to for a request to toggle [d] to be valid. *)

| req_toggle (d : door) (ω : Ω) (H : sel d ω = false -> sel (co d) ω = false)
  : req ω unit (Toggle d).

(** *** Promises *)

Inductive prom: Ω -> forall (a : Type), DOORS a -> a -> Prop :=

(** - When a system in a state [ω] reports the state of the door [d], it shall
      reflect the true state of [d]. *)

| prom_is_open (d : door) (ω : Ω) (x : bool) (equ : sel d ω = x)
  : prom ω bool (IsOpen d) x

(** - There is no particular promises on the result [x] of a request for [ω] to
      close the door [d]. *)

| prom_toggle (d : door) (ω : Ω) (x : unit)
  : prom ω unit (Toggle d) x.

Definition doors_specs : specs DOORS Ω := Build_specs _ _ step req prom.

(** ** Intermediary Lemmas *)

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

#[local] Arguments close_door : simpl never.
#[local] Arguments open_door : simpl never.
#[local] Arguments Nat.ltb : simpl never.

Fact one_door_safe_all_doors_safe (ω : Ω) (d : door)
    (safe : sel d ω = false \/ sel (co d) ω = false)
  : forall (d' : door), sel d' ω = false \/ sel (co d') ω = false.

Proof.
  intros d'.
  destruct d; destruct d'; auto.
  + cbn -[sel].
    now rewrite or_comm.
  + cbn -[sel].
    fold (co right).
    now rewrite or_comm.
Qed.

(** The objective of this lemma is to prove that, if either the right door or
    the left door is closed, then after any trustworthy run of a computation
    [p], this fact remains true. *)

Lemma trustworthy_run_inv {a} (p : impure DOORS a)
  (ω : Ω) (safe : sel left ω = false \/ sel right ω = false)
  (x : a) (ω' : Ω) (run : trustworthy_run doors_specs p ω ω' x)
  : sel left ω' = false \/ sel right ω' = false.


(** We reason by induction on the impure computation [p]:

    - Either [p] is a local, pure computation; in such a case, the doors state
      does not change, a the proof is trivial.

    - Or [p] consists in a request to the doors interface, and a continuation
      whose domain satisfies the theorem, _ie_, it preserves the invariant that
      either the left or the right door is closed.  Due to this hypothesis, we
      only have to prove that the first request made by [p] does not break the
      invariant. We consider two cases.

      - Either the computation asks for the state of a given door ([IsOpen]),
        then again the doors state does not change and the proof is trivial.
      - Or the computation wants to toggle a door [d].  We know by hypothesis
        that either [d] is closed or [d] is open (thanks to the
        [one_door_safe_all_doors_safe] result and the [safe] hypothesis).
        Again, we consider both cases.

         - If [d] is closed —and therefore will be opened—, then because we
           consider a trustworthy run, [co d] is necessarily closed too (it is a
           requirements of [door_specs]). Once [d] is opened, [co d] is still
           closed.
         - Otherwise, [co d] is closed, which means once [d] is toggled (no
           matter its initial state), then [co d] is still close.

         That is, we prove that, when [p] toggles [d], [co d] is necessarily
         closed after the request has been handled.  Because there is at least
         one door closed ([co d]), we can conclude that either the right or the
         left door is closed thanks to [one_door_safe_all_doors_safe]. *)

Proof.
  fold (co left) in *.
  revert ω run safe.
  induction p; intros ω run safe.
  + now unroll_impure_run run.
  + unroll_impure_run run.
    eapply H; eauto.
    destruct e as [d|d]; cbn -[sel] in *; auto.
    (* We try to toggle a door [d]. *)
    apply one_door_safe_all_doors_safe with (d := d).
    apply one_door_safe_all_doors_safe with (d' := d) in safe.
    inversion req0; ssubst.
    destruct safe as [safe | safe].
    (* 1. The door [d] is closed. Because we are in a trustworthy run, we
          know the door [co d] is also closed, and remains closed. *)
    ++ right.
       rewrite tog_equ_2.
       now apply H2.
    (* 2. The door [co d] is closed. Once [d] is toggled, [co d] will remain
          closed. *)
    ++ right.
       now rewrite tog_equ_2.
Qed.

(** ** Main Theorem *)

Lemma controller_correct
  : correct_component controller
                      (no_specs CONTROLLER)
                      doors_specs
                      (fun _ _ ω => sel left ω = false \/ sel right ω = false).
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

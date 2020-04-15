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
From FreeSpec.Core Require Import All.
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

Definition is_open `{Provide ix DOORS} (d : door) : impure ix bool :=
  request (IsOpen d).

Definition toggle `{Provide ix DOORS} (d : door) : impure ix unit :=
  request (Toggle d).

Definition open_door `{Provide ix DOORS} (d : door) : impure ix unit :=
  do let* open := is_open d in
     when (negb open) (toggle d)
  end.

Definition close_door `{Provide ix DOORS} (d : door) : impure ix unit :=
  do let* open := is_open d in
     when open (toggle d)
   end.

(** ** Controller *)

Inductive CONTROLLER : interface :=
| Tick : CONTROLLER unit
| RequestOpen (d : door) : CONTROLLER unit.

Definition tick `{Provide ix CONTROLLER} : impure ix unit :=
  request Tick.

Definition request_open `{Provide ix CONTROLLER} (d : door) : impure ix unit :=
  request (RequestOpen d).

Definition co (d : door) : door :=
  match d with
  | left => right
  | right => left
  end.

Definition controller `{Provide ix DOORS, Provide ix (STORE nat)} : component CONTROLLER ix :=
  fun _ op =>
    match op with
    | Tick =>
      do let* cpt := get in
         when (15 <? cpt) do
           close_door left;
           close_door right;
           put 0
         end
      end
    | RequestOpen d => do
        close_door (co d);
        open_door d;
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

#[local] Opaque tog.

Definition step (ω : Ω) (a : Type) (e : DOORS a) (x : a) :=
  match e with
  | Toggle d => tog d ω
  | _ => ω
  end.

(** *** Requirements *)

Inductive doors_o_caller : Ω -> forall (a : Type), DOORS a -> Prop :=

(** - Given the door [d] of o system [ω], it is always possible to ask for the
      state of [d]. *)

| req_is_open (d : door) (ω : Ω)
  : doors_o_caller ω bool (IsOpen d)

(** - Given the door [d] of o system [ω], if [d] is closed, then the second door
      [co d] has to be closed too for a request to toggle [d] to be valid. *)

| req_toggle (d : door) (ω : Ω) (H : sel d ω = false -> sel (co d) ω = false)
  : doors_o_caller ω unit (Toggle d).

(** *** Promises *)

Inductive doors_o_callee : Ω -> forall (a : Type), DOORS a -> a -> Prop :=

(** - When a system in a state [ω] reports the state of the door [d], it shall
      reflect the true state of [d]. *)

| doors_o_callee_is_open (d : door) (ω : Ω) (x : bool) (equ : sel d ω = x)
  : doors_o_callee ω bool (IsOpen d) x

(** - There is no particular doors_o_calleeises on the result [x] of a request for [ω] to
      close the door [d]. *)

| doors_o_callee_toggle (d : door) (ω : Ω) (x : unit)
  : doors_o_callee ω unit (Toggle d) x.

Definition doors_contract : contract DOORS Ω := make_contract step doors_o_caller doors_o_callee.

(** ** Intermediary Lemmas *)

(** Closing a door [d] in any system [ω] is always a respectful operation. *)

Lemma close_door_respectful `{Provide ix DOORS} (ω : Ω) (d : door)
  : respectful_impure doors_contract ω (close_door d).

Proof.
  (* We use the [prove_program] tactics to erase the program monad *)

  prove_impure; cbn; repeat constructor; subst.

  (* This leaves us with one goal to prove:

       [sel d ω = false -> sel (co d) ω = false]

     Yet, thanks to our call to [IsOpen d], we can predict that

       [sel d ω = true] *)

  inversion o_caller0; ssubst.
  now rewrite H3.
Qed.

Lemma open_door_respectful `{Provide ix DOORS} (ω : Ω)
    (d : door) (safe : sel (co d) ω = false)
  : respectful_impure doors_contract ω (open_door (ix := ix) d).

Proof.
  prove_impure; cbn; repeat constructor; subst.
  inversion o_caller0; ssubst.
  now rewrite safe.
Qed.

Lemma close_door_run `{Provide ix DOORS} (ω : Ω) (d : door) (ω' : Ω) (x : unit)
  (run : respectful_run doors_contract (close_door (ix := ix) d) ω ω' x)
  : sel d ω' = false.

Proof.
  unroll_respectful_run run; cbn in *.
  + rewrite tog_equ_1.
    inversion o_callee; ssubst.
    now rewrite H3.
  + now inversion o_callee; ssubst.
Qed.

#[local] Opaque close_door.
#[local] Opaque open_door.
#[local] Opaque Nat.ltb.

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
    the left door is closed, then after any respectful run of a computation
    [p] that interacts with doors, this fact remains true. *)

#[local] Opaque sel.

Lemma respectful_run_inv `{Provide ix DOORS} {a} (p : impure ix a)
  (ω : Ω) (safe : sel left ω = false \/ sel right ω = false)
  (x : a) (ω' : Ω) (run : respectful_run doors_contract p ω ω' x)
  : sel left ω' = false \/ sel right ω' = false.

(** We reason by induction on the impure computation [p]:

    - Either [p] is a local, pure computation; in such a case, the doors state
      does not change, hence the proof is trivial.

    - Or [p] consists in a request to the doors interface, and a continuation
      whose domain satisfies the theorem, i.e. it preserves the invariant that
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
           consider a respectful run, [co d] is necessarily closed too (it is a
           requirements of [door_contract]). Once [d] is opened, [co d] is still
           closed.
         - Otherwise, [co d] is closed, which means once [d] is toggled (no
           matter its initial state), then [co d] is still closed.

         That is, we prove that, when [p] toggles [d], [co d] is necessarily
         closed after the request has been handled.  Because there is at least
         one door closed ([co d]), we can conclude that either the right or the
         left door is closed thanks to [one_door_safe_all_doors_safe]. *)

Proof.
  fold (co left) in *.
  revert ω run safe.
  induction p; intros ω run safe.
  + now unroll_respectful_run run.
  + unroll_respectful_run run.
    destruct (proj_p e) as [ e' |].
    ++ eapply H1; eauto.
       destruct e' as [d|d]; cbn in *; auto.
       (* We try to toggle a door [d]. *)
       apply one_door_safe_all_doors_safe with (d := d).
       apply one_door_safe_all_doors_safe with (d' := d) in safe.
       inversion o_caller; ssubst.
       destruct safe as [safe | safe].
    (* 1. The door [d] is closed. Because we are in a respectful run, we
          know the door [co d] is also closed, and remains closed. *)
       +++ right.
           rewrite tog_equ_2.
           now apply H4.
    (* 2. The door [co d] is closed. Once [d] is toggled, [co d] will remain
          closed. *)
           +++ right.
               now rewrite tog_equ_2.
    ++ cbn in *.
       eapply H1; [ exact rec | exact safe ].
Qed.

(** ** Main Theorem *)

Lemma controller_correct `{ M1 : MayProvide ix DOORS
                          , P1 : @Provide ix DOORS M1
                          , M2 : MayProvide ix (STORE nat)
                          , P2 : @Provide ix (STORE nat) M2
                          , @Distinguish ix (STORE nat) DOORS M2 P2 M1
                          }
  : correct_component controller
                      (no_contract CONTROLLER)
                      doors_contract
                      (fun _ ω => sel left ω = false \/ sel right ω = false).

Proof.
  intros ωc ωd pred a e req.
  split.
  + destruct e.
    ++ prove_impure.
       +++ apply close_door_respectful.
       +++ apply close_door_respectful.
    ++ prove_impure.
       +++ apply close_door_respectful.
       +++ apply open_door_respectful.
           now apply close_door_run in Hrun.
  + intros x ωj' run.
    split; auto.
    eapply respectful_run_inv in run; auto.
Qed.

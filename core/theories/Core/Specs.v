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

From Prelude Require Import Tactics.
From FreeSpec.Core Require Export Program.

(** * Definition *)

Record specs (i : interface) (Ω : Type) : Type :=
  { witness (a : Type) (ω : Ω) : i a -> a -> Ω
  ; requirements (a : Type) (ω : Ω) : i a -> Prop
  ; promises (a : Type) (ω : Ω) : i a -> a -> Prop
  }.

Arguments witness [i Ω] (_) [a] (_ _ _).
Arguments requirements [i Ω] (_) [a] (_).
Arguments promises [i Ω] (_) [a] (_ _).

Definition no_req {i : interface} {Ω a} (ω : Ω) (e : i a) : Prop :=
  True.

Definition no_prom {i : interface} {Ω a} (ω : Ω) (e : i a) (x : a) : Prop :=
  True.

Definition no_specs (i : interface) : specs i unit :=
  {| witness := fun (a : Type) (u : unit) (e : i a) (x : a) => u
   ; requirements := @no_req i unit
   ; promises := @no_prom i unit
   |}.

(** * Composition *)

#[program]
Definition specsplus {i j Ωi Ωj} (speci : specs i Ωi) (specj : specs j Ωj)
  : specs (i ⊕ j) (Ωi * Ωj) :=
  {| witness := fun (a : Type) (ω : Ωi * Ωj) (e : (i ⊕ j) a) (x : a) =>
                  match e with
                  | in_left e => (witness speci (fst ω) e x, snd ω)
                  | in_right e => (fst ω, witness specj (snd ω) e x)
                  end
  ;  requirements := fun (a : Type) (ω : Ωi * Ωj) (e : (i ⊕ j) a) =>
                       match e with
                       | in_left e => requirements speci (fst ω) e
                       | in_right e => requirements specj (snd ω) e
                       end
  ;  promises := fun (a : Type) (ω : Ωi * Ωj) (e : (i ⊕ j) a) (x : a) =>
                   match e with
                   | in_left e => promises speci (fst ω) e x
                   | in_right e => promises specj (snd ω) e x
                   end
  |}.

Infix "'<.>'" := specsplus (at level 77, left associativity) : specs_scope.
Infix "'⊙'" := specsplus (at level 77, left associativity) : specs_scope.

(** * Trustworthiness *)

Inductive trustworthy_program {i a Ω} (c : specs i Ω) : Ω -> program i a -> Prop :=
| trustworthy_local
(** Given a term [x] and a witness [ω]… *)
    (x : a) (ω : Ω)
(** … the program [local x] is always trustworthy wrt. [c] in accordance to [ω]. *)
  : trustworthy_program c ω (local x)
| trustworthy_request {b}
(** Given an effect [e], a continuation [f], and a witness [ω]… *)
    (e : i b) (f : b -> program i a) (ω : Ω)
(** … if [e] satisfies [c] requirements *)
    (req : requirements c ω e)
(** … and [f] programs are trustworthy wrt. [c] in accordance to [ω'], where
    [ω'] is the witness after [e] interpretation… *)
    (prom : forall (x : b),
        promises c ω e x -> trustworthy_program c (witness c ω e x) (f x))
(** … then the program [request_then e f] is trustworthy wrt. [c] in accordance
    to [ω]. *)
  : trustworthy_program c ω (request_then e f).

Inductive trustworthy_run {i a Ω} (c : specs i Ω)
  : program i a -> Ω -> Ω -> a -> Prop :=
| run_local
(** Given a term [x], and an initial witness [ω]… *)
    (x : a) (ω : Ω)
(** … then a trustworthy run of [local x] produces a result [x] and a witness
    state [ω]. *)
  : trustworthy_run c (local x) ω ω x
| run_request {b}
(** Given an initial witness [ω]… *)
    (ω : Ω)
(** … an effect [e] which satisfies [c] requirements, and a continuation [f]… *)
    (e : i b) (req : requirements c ω e) (f : b -> program i a)
(** … a result [x] for [e] which satisfies [c] promises for [ω]… *)
    (x : b) (prom : promises c ω e x)
(** … if we can show that there is a trustworthy run of [f x] which produces a
    term [y] and a witness [ω']… *)
    (ω' : Ω) (y : a) (rec : trustworthy_run c (f x) (witness c ω e x) ω' y)
(** … then there is a trustworthy run of [request_then e f] which produces a
    result [y] and a witness [ω']. *)
  : trustworthy_run c (request_then e f) ω ω' y.

Lemma lm_trustworthy_bind_trustworthy_run {i a b Ω}
(** Given a specification [c] and a witness [ω]… *)
  (c : specs i Ω) (ω : Ω)
(** … a program of effects [p] and a continuation [f]… *)
  (p : program i a) (f : a -> program i b)
(** … if [p] is a trustworthy program wrt. [c] in accordance to [ω]… *)
  (trust : trustworthy_program c ω p)
(** … and for all result [x] and witness [ω'] produces by [p], [f x] is
    trustworthy… *)
  (run : forall (x : a) (ω' : Ω),
      trustworthy_run c p ω ω' x -> trustworthy_program c ω' (f x))
(** … then [local p f] is trustworthy. *)
  : trustworthy_program c ω (program_bind p f).

Proof.
  revert ω trust run.
  induction p; intros ω trust run.
  + apply run.
    constructor.
  + cbn.
    inversion trust; ssubst.
    constructor.
    ++ apply req.
    ++ intros y promx.
       apply H; [ auto |].
       intros z ω' run'.
       apply run.
       econstructor; eauto.
Qed.

Hint Resolve lm_trustworthy_bind_trustworthy_run : freespec_scope.

(** * Compliance *)

CoInductive compliant_semantics {i Ω} (c : specs i Ω) : Ω -> semantics i -> Prop :=
| compliant_semantics_rec
(** Given a semantics [sem], and a witness [ω]… *)
    (sem : semantics i) (ω : Ω)
(** … if [sem] computes results which satisfies [c] promises for effects which
    satisfies [c] requirements… *)
    (prom : forall {a} (e : i a),
        requirements c ω e -> promises c ω e (eval_effect sem e))
(** … and if the resulting semantics produces after interpreting [e] complies to
    [c] in accordance to [ω'], where [ω'] is the new witness state after [e]
    interpretation… *)
    (next : forall {a} (e : i a),
        requirements c ω e
        -> compliant_semantics c (witness c ω e (eval_effect sem e)) (exec_effect sem e))
(** … then [sem] complies to [c] in accordance to [ω] *)
  : compliant_semantics c ω sem.

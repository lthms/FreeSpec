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

From FreeSpec.Core Require Import CoreFacts.
From Coq Require Import Lia.

#[local] Open Scope nat_scope.

Create HintDb counter.

Generalizable All Variables.

(** The goal of this file is to provide a simple test case for [prove_impure]
    and [unroll_respectful_run]. *)

Inductive COUNTER : interface :=
| Get : COUNTER nat
| Inc : COUNTER unit
| Dec : COUNTER unit.

Definition counter_get `{Provide ix COUNTER} : impure ix nat :=
  request Get.

Definition counter_inc `{Provide ix COUNTER} : impure ix unit :=
  request Inc.

Definition counter_dec `{Provide ix COUNTER} : impure ix unit :=
  request Dec.

Fixpoint repeat {m : Type -> Type} `{Monad m} {a} (n : nat) (c : m a) : m unit :=
  match n with
  | O => pure tt
  | S n => (c >>= fun _ => repeat n c)
  end.

Definition update_counter (x : nat) : forall (a : Type), COUNTER a -> a -> nat :=
  fun (a : Type) (p : COUNTER a) (_ : a) =>
    match p with
    | Inc => S x
    | Dec => Nat.pred x
    | _ => x
    end.

Definition counter_o_caller (x : nat) : forall (a : Type), COUNTER a -> Prop :=
  fun (a : Type) (p : COUNTER a) =>
    match p with
    | Dec => 0 < x
    | _ => True
    end.

Definition counter_o_callee (x : nat) : forall (a : Type), COUNTER a -> a -> Prop :=
  fun (a : Type) (p : COUNTER a) (r : a) =>
    match p, r with
    | Get, r => r = x
    | _, _ => True
    end.

Definition counter_specs : contract COUNTER nat :=
  {| witness_update := update_counter
   ; caller_obligation := counter_o_caller
   ; callee_obligation := counter_o_callee
   |}.

Definition dec_then_inc `{Provide ix COUNTER} (x y : nat) : impure ix nat :=
  repeat x counter_dec;;
  repeat y counter_inc;;
  counter_get.

Theorem dec_then_inc_respectful `{Provide ix COUNTER} (cpt x y : nat)
    (init_cpt : x < cpt)
  : pre (to_hoare counter_specs $ dec_then_inc x y) cpt.

Proof.
  prove impure.
  + revert x cpt init_cpt.
    induction x; intros cpt init_cpt; prove impure.
    ++ cbn.
       transitivity (S x); auto.
       apply PeanoNat.Nat.lt_0_succ.
    ++ apply IHx.
       now apply Lt.lt_pred.
  + clear init_cpt hpost cpt.
    revert ω; induction y; intros cpt; prove impure.
Qed.

Lemma repeat_dec_cpt_output
   `(run : post (to_hoare counter_specs $ repeat x counter_dec) cpt r cpt')
    (init_cpt : x < cpt)
  : cpt' = cpt - x.

Proof.
  revert init_cpt run; revert cpt; induction x; intros cpt init_cpt run.
  + unroll_post run.
    now rewrite PeanoNat.Nat.sub_0_r.
  + unroll_post run.
    apply IHx in run; [| lia].
    subst.
    lia.
Qed.

Hint Resolve repeat_dec_cpt_output : counter.

Lemma repeat_inc_cpt_output
   `(run : post (to_hoare counter_specs $ repeat x counter_inc) cpt r cpt')
  : cpt' = cpt + x.

Proof.
  revert run; revert cpt; induction x; intros cpt run.
  + unroll_post run.
    now rewrite PeanoNat.Nat.add_0_r.
  + unroll_post run.
    apply IHx in run.
    lia.
Qed.

Hint Resolve repeat_inc_cpt_output : counter.

Lemma get_cpt_output (cpt x cpt' : nat)
    (run : post (to_hoare counter_specs $ counter_get) cpt x cpt')
  : cpt' = cpt.

Proof.
  now unroll_post run.
Qed.

Hint Resolve get_cpt_output : counter.

#[local]
Opaque counter_get.

Theorem dec_then_inc_cpt_output (cpt x y cpt' r : nat)
    (init_cpt : x < cpt)
    (run : post (to_hoare counter_specs $ dec_then_inc x y) cpt r cpt')
  : cpt' = cpt - x + y.

Proof.
  unroll_post run.
  apply repeat_dec_cpt_output in run0; [| exact init_cpt ].
  apply repeat_inc_cpt_output in run.
  apply get_cpt_output in run2.
  lia.
Qed.

#[local]
Transparent counter_get.

Theorem dec_then_inc_output (cpt x y cpt' r : nat)
    (init_cpt : x < cpt)
    (run : post (to_hoare counter_specs $ dec_then_inc x y) cpt r cpt')
  : cpt' = r.

Proof.
  now unroll_post run.
Qed.

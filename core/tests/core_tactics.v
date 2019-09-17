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

From FreeSpec Require Import Core.
From Coq Require Import Lia.

Generalizable All Variables.

(** The goal of this file is to provide a simple test case for [prove_impure]
    and [unroll_impure_run]. *)

Inductive COUNTER : interface :=
| Get : COUNTER nat
| Inc : COUNTER unit
| Dec : COUNTER unit.

Definition counter_get `{ix :| COUNTER} : impure ix nat :=
  request Get.

Definition counter_inc `{ix :| COUNTER} : impure ix unit :=
  request Inc.

Definition counter_dec `{ix :| COUNTER} : impure ix unit :=
  request Dec.

Fixpoint repeat `{Monad m} {a} (n : nat) (c : m a) : m unit :=
  match n with
  | O => pure tt
  | S n => c >>= fun _ => repeat n c
  end.

Definition update_counter (x : nat) : forall (a : Type), COUNTER a -> a -> nat :=
  fun (a : Type) (p : COUNTER a) (_ : a) =>
    match p with
    | Inc => S x
    | Dec => pred x
    | _ => x
    end.

Definition counter_req (x : nat) : forall (a : Type), COUNTER a -> Prop :=
  fun (a : Type) (p : COUNTER a) =>
    match p with
    | Dec => 0 < x
    | _ => True
    end.

Definition counter_promises (x : nat) : forall (a : Type), COUNTER a -> a -> Prop :=
  fun (a : Type) (p : COUNTER a) (r : a) =>
    match p, r with
    | Get, r => r = x
    | _, _ => True
    end.

Definition counter_specs : specs COUNTER nat :=
  {| witness_update := update_counter
   ; requirements := counter_req
   ; promises := counter_promises
   |}.

Definition dec_then_inc `{ix :| COUNTER} (x y : nat) : impure ix nat :=
  do repeat x counter_dec;
     repeat y counter_inc;
     counter_get
   end.

Theorem dec_then_inc_trustworthy (cpt x y : nat)
    (init_cpt : x < cpt)
  : trustworthy_impure counter_specs cpt (dec_then_inc x y).

Proof.
  prove_impure.
  + revert x cpt init_cpt.
    induction x; intros cpt init_cpt; prove_impure.
    ++ cbn.
       transitivity (S x); auto.
       apply PeanoNat.Nat.lt_0_succ.
    ++ apply IHx.
       now apply Lt.lt_pred.
  + clear init_cpt Hrun cpt.
    revert w; induction y; intros cpt; prove_impure.
    ++ constructor.
    ++ apply IHy.
  + unfold counter_get.
    prove_impure.
    constructor.
Qed.

Lemma repeat_dec_cpt_output (cpt x cpt' : nat) (init_cpt : x < cpt)
    (run : trustworthy_run counter_specs (repeat x counter_dec) cpt cpt' tt)
  : cpt' = cpt - x.

Proof.
  revert init_cpt run; revert cpt; induction x; intros cpt init_cpt run.
  + unroll_impure_run run.
    now rewrite PeanoNat.Nat.sub_0_r.
  + unroll_impure_run run.
    apply IHx in rec; [| lia ].
    rewrite rec.
    lia.
Qed.

Lemma repeat_inc_cpt_output (cpt x cpt' : nat)
    (run : trustworthy_run counter_specs (repeat x counter_inc) cpt cpt' tt)
  : cpt' = cpt + x.

Proof.
  revert run; revert cpt; induction x; intros cpt run.
  + unroll_impure_run run.
    now rewrite PeanoNat.Nat.add_0_r.
  + unroll_impure_run run.
    apply IHx in rec.
    rewrite rec.
    lia.
Qed.

Lemma get_cpt_output (cpt x cpt' : nat)
    (run : trustworthy_run counter_specs counter_get cpt cpt' x)
  : cpt' = cpt.

Proof.
  unfold counter_get, request in run.
  now unroll_impure_run run.
Qed.

Theorem dec_then_inc_cpt_output (cpt x y cpt' r : nat)
    (init_cpt : x < cpt)
    (run : trustworthy_run counter_specs (dec_then_inc x y) cpt cpt' r)
  : cpt' = cpt - x + y.
Proof.
  unroll_impure_run run.
  destruct y0; apply repeat_dec_cpt_output in run0; [| exact init_cpt ].
  destruct y1; apply repeat_inc_cpt_output in run.
  apply get_cpt_output in run2; lia.
Qed.

Theorem dec_then_inc_output (cpt x y cpt' r : nat)
    (init_cpt : x < cpt)
    (run : trustworthy_run counter_specs (dec_then_inc x y) cpt cpt' r)
  : cpt' = r.
Proof.
  unroll_impure_run run.
  unfold counter_get in run2.
  unroll_impure_run run2.
  now inversion prom.
Qed.

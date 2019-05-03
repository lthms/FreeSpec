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

(* begin hide *)
Require Import Coq.Program.Equality.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Logic.Classical.
Require Import Coq.Setoids.Setoid.
(* end hide *)

Require Import FreeSpec.Semantics.
Require Import FreeSpec.Program.
Require Import FreeSpec.Specification.

Require Import Prelude.Equality.

(** * Temporal Logic [Formula]

    ** [Dec]idable Proprety

    A Decidable Property is a predicate for which an answer can be
    computed. Not all predicate can be easily turned into decidable
    properties.

 *)

Record Dec
       (A: Type) :=
  { prop: A -> Prop
  ; prop_dec (x:  A): { prop x } + { ~ prop x }
  }.

Arguments prop [A] (_ _).
Arguments prop_dec [A] (_ _).


(** We define two notations, [p? a] and [p.? a] to use either the
    predicate or the decidable version of the predicate.

 *)

Notation "p ? a" := (prop_dec p a) (at level 51): dec_scope.
Notation "p .? a" := (prop p a) (at level 51): dec_scope.

Local Open Scope dec_scope.

Inductive sat
          (A B:  Prop)
  : { A } + { B } -> Prop :=
| IsSat (x: A)
  : sat A B (left x).

Arguments sat {A B} (_).
Arguments IsSat {A B} (_).

Inductive unsat
          (A B:  Prop)
  : { A } + { B } -> Prop :=
| IsUnsat (x: B)
  : unsat A B (right x).

Arguments unsat {A B} (_).
Arguments IsUnsat {A B} (_).

Lemma prop_dec_prop
      {A: Type}
      (p: Dec A)
      (a: A)
  : sat (p? a) <-> p.? a.
Proof.
  split.
  + now intros [H].
  + intros H.
    now destruct (p ? a).
Qed.

Lemma prop_bool_false
      {A: Type}
      (p: Dec A)
      (a: A)
  : unsat (p? a) <-> ~ p.? a.
Proof.
  split.
  + now intros [H] F.
  + intros H.
    now destruct (p? a).
Qed.

Local Open Scope prelude_scope.

(** ** [Formula] Definition

 *)

Inductive Formula
          (A: Type)
  : Type :=
| ltrue
  : Formula A
| lfalse
  : Formula A
| globally (prop: Dec A)
  : Formula A
| eventually (prop: Dec A)
  : Formula A
| next (tl: Formula A)
  : Formula A
| switch (tl1: Formula A)
         (prop: Dec A)
         (tl2: Formula A)
  : Formula A.

Arguments ltrue [_].
Arguments lfalse [_].
Arguments globally [_] (_).
Arguments eventually [_] (_).
Arguments next [_] (_).
Arguments switch [_] (_ _ _).

Fixpoint halt_satisfies
         {A: Type}
         (tl: Formula A)
  : Prop :=
  match tl with
  | eventually _ => False
  | next _ => False
  | switch before _ _ => halt_satisfies before
  | _ => True
  end.

#[program]
Fixpoint halt_satisfies_dec
         {A: Type}
         (tl: Formula A)
  : { halt_satisfies tl } + { ~ halt_satisfies tl } :=
  match tl with
  | eventually _ => ltac:(right)
  | next _ => ltac:(right)
  | switch before _ _ => halt_satisfies_dec before
  | ltrue | lfalse | globally _ => ltac:(left)
  end.

Inductive Formula_step
          {A: Type}
  : Formula A -> Formula A -> Prop :=
| ltrue_stays_ltrue: Formula_step ltrue ltrue
| lfalse_stays_lfalse: Formula_step lfalse lfalse
| globally_stays_globally
    (prop: Dec A)
  : Formula_step (globally prop) (globally prop)
| globally_can_fail
    (prop: Dec A)
  : Formula_step (globally prop) lfalse
| eventually_stays_eventually
    (prop: Dec A)
  : Formula_step (eventually prop) (eventually prop)
| eventually_can_succeed
    (prop: Dec A)
  : Formula_step (eventually prop) ltrue
| next_steps_unwrap
    (tl: Formula A)
  : Formula_step (next tl) tl
| switch_steps_before
    (tl1 tl2 tl3: Formula A)
    (prop: Dec A)
    (Hderive: Formula_step tl1 tl2)
  : Formula_step (switch tl1 prop tl3) (switch tl2 prop tl3)
| switch_step_after_small
    (tl1 tl2: Formula A)
    (prop: Dec A)
  : Formula_step (switch tl1 prop tl2) tl2
| switch_can_fail
    (tl1 tl2: Formula A)
    (prop: Dec A)
  : Formula_step (switch tl1 prop tl2) lfalse.

Arguments ltrue_stays_ltrue [_].
Arguments lfalse_stays_lfalse [_].
Arguments globally_stays_globally [_] (_).
Arguments globally_can_fail [_] (_).
Arguments eventually_stays_eventually [_] (_).
Arguments eventually_can_succeed [_] (_).
Arguments next_steps_unwrap [_] (_).
Arguments switch_steps_before [_] (_ _ _ _ _).
Arguments switch_step_after_small [_] (_ _ _).
Arguments switch_can_fail [_] (_ _ _).

Fixpoint effect_satisfies
         {A: Type}
         (a: A)
         (tl: Formula A)
  : Prop :=
  match tl with
  | ltrue => True
  | lfalse => False
  | globally prop => prop.? a
  | eventually tl => True
  | next _
    => True
  | switch before prop after
    => (prop.? a -> effect_satisfies a after
                    /\ halt_satisfies before)
       /\ (~prop.? a -> effect_satisfies a before)
  end.

Ltac anddec a b := refine (if sumbool_and _ _ _ _ a b then ltac:(left) else ltac:(right)).
Ltac sat a := refine (if a then ltac:(left) else ltac:(right)).

#[program]
Fixpoint effect_satisfies_dec
         {A: Type}
         (a: A)
         (tl: Formula A)
  : { effect_satisfies a tl } + { ~ effect_satisfies a tl } :=
  match tl with
  | ltrue
    => ltac:(left)
  | lfalse
    => ltac:(right)
  | globally prop
    => prop? a
  | eventually prop
    => ltac:(left)
  | next _
    => ltac:(left)
  | switch before p after
    => if p? a
       then ltac:(anddec (effect_satisfies_dec _ a after)
                         (halt_satisfies_dec before))
       else ltac:(sat (effect_satisfies_dec _ a before))
  end.

Next Obligation.
  now repeat split.
Defined.

Next Obligation.
  destruct H0 as [not_effect | not_halt];
    now intros [[H1 H2] H3].
Defined.

Next Obligation.
  now repeat split.
Defined.

Next Obligation.
  intros [H1 H2].
  now apply H2 in H.
Defined.

#[program]
Fixpoint tl_step
         {A: Type}
         (a: A)
         (tl: Formula A)
  : { tl' | Formula_step tl tl' } :=
  match tl with
  | next tl
    => tl
  | switch before p after
    => if p? a
       then after
       else switch (tl_step a before) p after
  | eventually p
    => if p ? a
       then ltrue
       else eventually p
  | globally p
    => if p ? a
       then globally p
       else lfalse
  | ltrue
    => ltrue
  | lfalse
    => lfalse
  end.

Next Obligation.
  constructor.
Defined.

Next Obligation.
  constructor.
Defined.

Next Obligation.
  now constructor.
Defined.

Next Obligation.
  constructor.
Defined.

Next Obligation.
  constructor.
Defined.

Next Obligation.
  constructor.
Defined.

Next Obligation.
  constructor.
Defined.

Next Obligation.
  constructor.
Defined.

Next Obligation.
  constructor.
Defined.

Inductive ISet
          (I: Type -> Type)
  : Type :=
  | effect {A: Type}
                (i: I A)
    : ISet I.

Arguments effect [_ _].

Inductive Formula_run
          {A: Type}
  : Formula A -> Formula A -> Prop :=
| tl_run_refl
    (tl: Formula A)
  : Formula_run tl tl
| tl_run_small_step
    (from to: Formula A)
    (Hstep: Formula_step from to)
  : Formula_run from to
| tl_run_big_step
    (from tl to: Formula A)
    (Hstep: Formula_step from tl)
    (Hrun: Formula_run tl to)
  : Formula_run from to.

Lemma tl_step_run_trans
      {A: Type}
      (tl tl' tl'': Formula A)
  : Formula_step tl tl'
    -> Formula_step tl' tl''
    -> Formula_run tl tl''.
Proof.
  intros H1 H2.
  apply (tl_run_big_step tl tl' tl'').
  + exact H1.
  + apply (tl_run_small_step tl' tl'' H2).
Qed.

Lemma tl_run_step_run
      {A: Type}
      (tl tl' tl'': Formula A)
  : Formula_run tl tl'
    -> Formula_step tl' tl''
    -> Formula_run tl tl''.
Proof.
  intros H1 H2.
  induction H1.
  ++ constructor.
     exact H2.
  ++ apply (tl_step_run_trans from to tl'' Hstep H2).
  ++ apply IHFormula_run in H2.
     apply (tl_run_big_step from tl tl'' Hstep H2).
Qed.

Lemma tl_run_trans
      {A: Type}
      (tl tl' tl'': Formula A)
  : Formula_run tl tl'
    -> Formula_run tl' tl''
    -> Formula_run tl tl''.
Proof.
  intros H1 H2.
  induction H1.
  + exact H2.
  + apply (tl_run_big_step from to tl'' Hstep H2).
  + apply IHFormula_run in H2.
    apply (tl_run_big_step from tl tl'' Hstep H2).
Qed.

Lemma next_derives_big
      {A: Type}
      (tl tl': Formula A)
      (Hderive: Formula_run tl tl')
  : Formula_run (next tl) tl'.
Proof.
  assert (Formula_run (next tl) tl)
    as Hbefore
      by (repeat constructor).
  apply (tl_run_trans (next tl) tl tl' Hbefore Hderive).
Qed.

Lemma switch_derives_after_big
      {A: Type}
      (tl1 tl2 tl3: Formula A)
      (prop: Dec A)
      (Hderive: Formula_run tl2 tl3)
  : Formula_run (switch tl1 prop tl2) tl3.
Proof.
  assert (Formula_run (switch tl1 prop tl2) tl2)
    as Hrun'
      by (repeat constructor).
  apply (tl_run_trans (switch tl1 prop tl2) tl2 tl3 Hrun' Hderive).
Qed.

Lemma switch_derives_before_big
      {A: Type}
      (tl1 tl2 tl3: Formula A)
      (prop: Dec A)
      (Hderive: Formula_run tl1 tl2)
  : Formula_run (switch tl1 prop tl3) (switch tl2 prop tl3).
Proof.
  induction Hderive.
  + apply tl_run_refl.
  + apply tl_run_small_step.
    constructor.
    exact Hstep.
  + apply (tl_run_trans (switch from prop tl3) (switch tl prop tl3)).
    ++ repeat constructor.
       exact Hstep.
    ++ exact IHHderive.
Qed.

#[program]
Definition deriveFormula
           {I: Interface}
           {A: Type}
           (sig: Sem.t I)
           (p: Program I A)
           (tl: Formula (ISet I)) :=
    witnessInstrumentedProgram (fun (R: Type) (e: I R) (_: R) => tl_step (effect e)) tl sig p.

#[program]
Definition runFormula
           {I: Interface}
           {A: Type}
           (sig: Sem.t I)
           (p: Program I A)
           (tl: Formula (ISet I)) :=
    runInstrumentedProgram (fun (R: Type) (e: I R) (_: R) => tl_step (effect e)) tl sig p.

Lemma Formula_run_is_runFormula
  : forall {I: Type -> Type}
           {A: Type}
           (p: Program I A)
           (tl: Formula (ISet I))
           (sig: Sem.t I),
    Formula_run tl (deriveFormula sig p tl).
Proof.
  induction p.
  + intros tl sig.
    cbn.
    apply tl_run_refl.
  + intros tl sig.
    cbn.
    eapply (tl_run_trans tl (proj1_sig (tl_step (effect e) tl))).
    ++ constructor.
       apply (proj2_sig (tl_step (effect e) tl)).
    ++ apply H.
Qed.

Inductive Formula_derive
          {A: Type}
  : Formula A -> Formula A -> Prop :=
| tl_derives_tl
    (x: Formula A)
  : Formula_derive x x
| ltrue_derives_ltrue
  : Formula_derive ltrue ltrue
| lfalse_derives_lfalse
  : Formula_derive lfalse lfalse
| globally_derives_globally
    (prop: Dec A)
  : Formula_derive (globally prop) (globally prop)
| globally_derives_fail
    (prop: Dec A)
  : Formula_derive (globally prop) lfalse
| eventually_derives_eventually
    (prop: Dec A)
  : Formula_derive (eventually prop) (eventually prop)
| eventually_derives_fail
    (prop: Dec A)
  : Formula_derive (eventually prop) ltrue
| next_derives_unwrap
    (tl tl': Formula A)
    (Hderive: Formula_derive tl tl')
  : Formula_derive (next tl) tl'
| switch_derives_before
    (before after tl: Formula A)
    (prop: Dec A)
    (Hderive: Formula_derive before tl)
  : Formula_derive (switch before prop after) (switch tl prop after)
| switch_derives_after
    (before after tl: Formula A)
    (prop: Dec A)
    (Hderive: Formula_derive after tl)
  : Formula_derive (switch before prop after) tl
| switch_derives_fail
    (before after: Formula A)
    (prop: Dec A)
  : Formula_derive (switch before prop after) lfalse.

Arguments tl_derives_tl [_].
Arguments ltrue_derives_ltrue [_].
Arguments lfalse_derives_lfalse [_].
Arguments globally_derives_globally [_].
Arguments globally_derives_fail [_].
Arguments eventually_derives_eventually [_].
Arguments eventually_derives_fail [_].
Arguments next_derives_unwrap [_].
Arguments switch_derives_before [_].
Arguments switch_derives_after [_].
Arguments switch_derives_fail [_].

Lemma tl_step_is_tl_derive
      {A: Type}
  : forall (tl tl': Formula A),
    Formula_step  tl tl' -> Formula_derive tl tl'.
Proof.
  induction tl; intros; inversion H; subst.
  + constructor.
  + constructor.
  + constructor.
  + constructor.
  + constructor.
  + constructor.
  + constructor; constructor.
  + constructor.
    apply IHtl1.
    exact Hderive.
  + constructor; constructor.
  + apply switch_derives_fail.
Qed.

Lemma tl_run_implies_tl_derive
      {A: Type}
  : forall (tl tl': Formula A),
    Formula_derive tl tl' -> Formula_run  tl tl'.
Proof.
  induction tl.
  + intros tl' Hderive.
    inversion Hderive; subst; constructor.
  + intros tl' Hderive.
    inversion Hderive; subst; constructor.
  + intros tl' Hderive.
    inversion Hderive; subst; repeat constructor.
  + intros tl' Hderive.
    inversion Hderive; subst; repeat constructor.
  + intros tl' Hderive.
    inversion Hderive; subst.
    ++ apply tl_run_refl.
    ++ assert (Formula_run (next tl) tl)
        as Hstep
          by (repeat constructor).
       apply (tl_run_trans (next tl) tl tl' Hstep).
       apply IHtl.
       apply Hderive0.
  + intros tl' Hderive.
    inversion Hderive; subst.
    ++ apply tl_run_refl.
    ++ apply (switch_derives_before_big tl1 tl tl2).
       apply IHtl1.
       exact Hderive0.
    ++ apply (switch_derives_after_big tl1 tl2 tl').
       apply IHtl2.
       exact Hderive0.
    ++ repeat constructor.
Qed.

Lemma switch_derives_before_helper
      {A: Type}
      (tl1 tl2 tl3: Formula A)
      (prop: Dec A)
      (Hderive: Formula_derive tl1 tl2)
  : Formula_derive (switch tl1 prop tl3) (switch tl2 prop tl3).
Proof.
  induction Hderive.
  + constructor.
  + constructor.
  + constructor.
  + constructor.
  + repeat constructor.
  + constructor.
  + repeat constructor.
  + apply switch_derives_before.
    constructor.
    exact Hderive.
  + apply switch_derives_before.
    apply switch_derives_before.
    exact Hderive.
  + apply switch_derives_before.
    apply switch_derives_after.
    exact Hderive.
  + apply switch_derives_before.
    apply switch_derives_fail.
Qed.

Lemma tl_derive_trans'
      {A: Type}
  : forall (tl tl': Formula A),
    Formula_derive tl tl' -> (forall (tl'': Formula A), Formula_derive tl' tl'' -> Formula_derive tl tl'').
Proof.
  intros tl tl' H1; induction H1; intros tl'' H2; try exact H2.
  + inversion_clear H2;
      constructor.
  + inversion_clear H2;
      constructor.
  + constructor.
    apply (IHFormula_derive tl'' H2).
  + inversion_clear H2.
    ++ apply switch_derives_before_helper.
       exact H1.
    ++ apply switch_derives_before_helper.
       apply (IHFormula_derive tl0 Hderive).
    ++ apply switch_derives_after.
       exact Hderive.
    ++ apply switch_derives_fail.
  + apply switch_derives_after.
    apply IHFormula_derive in H2.
    exact H2.
  + inversion_clear H2.
    ++ apply switch_derives_fail.
    ++ apply switch_derives_fail.
Qed.

Lemma tl_derive_trans
      {A: Type}
  : forall (tl tl' tl'': Formula A),
    Formula_derive tl tl' -> Formula_derive tl' tl'' -> Formula_derive tl tl''.
Proof.
  intros tl tl' tl'' H1 H2.
  apply (tl_derive_trans' tl tl' H1 tl'' H2).
Qed.

Lemma tl_derive_implies_tl_run
      {A: Type}
  : forall (tl tl': Formula A),
    Formula_run tl tl' -> Formula_derive  tl tl'.
Proof.
  intros.
  induction H.
  + constructor.
  + apply tl_step_is_tl_derive in Hstep.
    exact Hstep.
  + apply tl_step_is_tl_derive in Hstep.
    apply (tl_derive_trans from tl to Hstep IHFormula_run).
Qed.

Theorem derive_is_run_and_run_is_derive
        {A: Type}
        (tl tl': Formula A)
  : Formula_run tl tl' <-> Formula_derive tl tl'.
Proof.
  split.
  + apply tl_derive_implies_tl_run.
  + apply tl_run_implies_tl_derive.
Qed.

Corollary Formula_derive_is_runFormula
  : forall {I: Type -> Type}
           {A: Type}
           (p: Program I A)
           (tl: Formula (ISet I))
           (sig: Sem.t I),
    Formula_derive tl (deriveFormula sig p tl).
Proof.
  intros I A p tl sig.
  apply tl_derive_implies_tl_run.
  apply Formula_run_is_runFormula.
Qed.

Lemma tl_run_switch_before
      {A: Type}
  : forall (tl tl' tl2: Formula A)
           (prop: Dec A),
    Formula_run tl tl'
    -> Formula_run (switch tl prop tl2) (switch tl' prop tl2).
Proof.
  intros tl tl' tl2 prop Hrun.
  apply tl_run_implies_tl_derive.
  apply tl_derive_implies_tl_run in Hrun.
  apply switch_derives_before.
  exact Hrun.
Qed.

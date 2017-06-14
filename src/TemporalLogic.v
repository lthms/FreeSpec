(* begin hide *)
Require Import Coq.Program.Equality.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Logic.Classical.
Require Import Coq.Setoids.Setoid.
(* end hide *)

Require Import FreeSpec.Utils.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Program.
Require Import FreeSpec.Equiv.
Require Import FreeSpec.Abstract.

(** * Temporal Logic [Formula]

    ** [Dec]idable Proprety

    A Decidable Property is a predicate for which an answer can be
    computed. Not all predicate can be easily turned into decidable
    properties.

 *)

Record Dec
       (A: Type) :=
  { prop: A -> Prop
  ; prop_dec: forall (a: A), {prop a}+{~prop a}
  }.

Arguments prop [A] (_ _).
Arguments prop_dec [A] (_ _).

(** We define two notations, [p? a] and [p.? a] to use either the
    predicate or the decidable version of the predicate.

 *)

Notation "p ? a" := (prop_dec p a) (at level 51): dec_scope.
Notation "p .? a" := (prop p a) (at level 51): dec_scope.

Local Open Scope dec_scope.
Local Open Scope eq_scope.

(** ** [Formula] Definition

 *)

Inductive Formula
          (A: Type)
  : Type :=
| true
  : Formula A
| false
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

Arguments true [_].
Arguments false [_].
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

Fixpoint halt_satisfies_dec
         {A: Type}
         (tl: Formula A)
  : {halt_satisfies tl}+{~halt_satisfies tl}.
  refine (
      match tl with
      | eventually _ => false_dec
      | next _ => false_dec
      | switch before _ _ => decide_dec (halt_satisfies_dec A before)
      | _ => true_dec
      end);
    cbn;
    firstorder.
Defined.

Inductive Formula_step
          {A: Type}
  : Formula A -> Formula A -> Prop :=
| true_stays_true: Formula_step true true
| false_stays_false: Formula_step false false
| globally_stays_globally
    (prop: Dec A)
  : Formula_step (globally prop) (globally prop)
| globally_can_fail
    (prop: Dec A)
  : Formula_step (globally prop) false
| eventually_stays_eventually
    (prop: Dec A)
  : Formula_step (eventually prop) (eventually prop)
| eventually_can_succeed
    (prop: Dec A)
  : Formula_step (eventually prop) true
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
  : Formula_step (switch tl1 prop tl2) false.

Arguments true_stays_true [_].
Arguments false_stays_false [_].
Arguments globally_stays_globally [_] (_).
Arguments globally_can_fail [_] (_).
Arguments eventually_stays_eventually [_] (_).
Arguments eventually_can_succeed [_] (_).
Arguments next_steps_unwrap [_] (_).
Arguments switch_steps_before [_] (_ _ _ _ _).
Arguments switch_step_after_small [_] (_ _ _).
Arguments switch_can_fail [_] (_ _ _).

Fixpoint instruction_satisfies
         {A: Type}
         (a: A)
         (tl: Formula A)
  : Prop :=
  match tl with
  | true => True
  | false => False
  | globally prop => prop.? a
  | eventually tl => True
  | next _
    => True
  | switch before prop after
    => (prop.? a -> instruction_satisfies a after
                    /\ halt_satisfies before)
       /\ (~prop.? a -> instruction_satisfies a before)
  end.

Fixpoint instruction_satisfies_dec
         {A: Type}
         (a: A)
         (tl: Formula A)
  : {instruction_satisfies a tl}+{~instruction_satisfies a tl}.
  refine (
      match tl with
      | true
        => true_dec
      | false
        => false_dec
      | globally prop
        => decide_dec (prop? a)
      | eventually prop
        => true_dec
      | next _
        => true_dec
      | switch before p after
        => if p? a
           then decide_dec (sumbool_and _ _ _ _
                                        (instruction_satisfies_dec A a after)
                                        (halt_satisfies_dec before))
           else decide_dec (instruction_satisfies_dec A a before)
      end
    ); cbn; trivial.
  + intro False; destruct False.
  + split.
    ++ intro _H; exact a0.
    ++ intro False; apply False in p0; destruct p0.
  + intro False.
    destruct False as [False _H].
    apply False in p0.
    apply or_not_and in o.
    apply o in p0.
    destruct p0.
  + split.
    ++ intro False; apply n in False; destruct False.
    ++ intro _H; exact i.
  + intro False.
    destruct False as [_H False].
    apply False in n.
    apply n0 in n.
    destruct n.
Defined.

Fixpoint tl_step
         {A: Type}
         (a: A)
         (tl: Formula A)
  : Formula A :=
  if instruction_satisfies_dec a tl
  then match tl with
       | next tl
         => tl
       | switch before p after
         => if p? a
            then after
            else switch (tl_step a before) p after
       | eventually p
         => if p ? a
            then true
            else eventually p
       | x
         => x
       end
  else false.

Lemma Formula_step_is_tl_step
      {A: Type}
      (a: A)
      (tl: Formula A)
  : Formula_step tl (tl_step a tl).
Proof.
  induction tl.
  + constructor.
  + constructor.
  + cbn; destruct (prop0 ? a); constructor.
  + cbn; destruct (prop0 ? a); constructor.
  + cbn; constructor.
  + cbn.
    destruct (prop0 ? a).
    ++ destruct (instruction_satisfies_dec a tl2);
         destruct (halt_satisfies_dec tl1);
         cbn.
       +++ constructor.
       +++ constructor.
       +++ constructor.
       +++ constructor.
    ++ destruct (instruction_satisfies_dec a tl1).
       +++ constructor.
           exact IHtl1.
       +++ constructor.
Qed.

Inductive ISet
          (I: Type -> Type)
  : Type :=
  | instruction {A: Type}
                (i: I A)
    : ISet I.

Arguments instruction [_ _].

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

Definition deriveFormula
           {I: Interface}
           {A: Type}
           (int: Interp I)
           (p: Program I A)
           (tl: Formula (ISet I)) :=
    deriveAbstraction tl (fun (R: Type) (i: I R) => tl_step (instruction i)) int p.

Definition runFormula
           {I: Interface}
           {A: Type}
           (int: Interp I)
           (p: Program I A)
           (tl: Formula (ISet I)) :=
    abstractRun tl (fun (R: Type) (i: I R) => tl_step (instruction i)) int p.

Lemma Formula_run_is_runFormula
  : forall {I: Type -> Type}
           {A: Type}
           (p: Program I A)
           (tl: Formula (ISet I))
           (int: Interp I),
    Formula_run tl (deriveFormula int p tl).
Proof.
  induction p.
  + intros tl int.
    cbn.
    apply tl_run_refl.
  + intros tl int.
    cbn.
    constructor.
    apply Formula_step_is_tl_step.
  + intros tl int.
    cbn.
    apply (tl_run_trans tl
                        (snd (runFormula int p tl))
                        (snd
                           (runFormula (snd (fst (runFormula int p tl))) (f (fst (fst (runFormula int p tl))))
                                  (snd (runFormula int p tl))))).
    ++ apply IHp.
    ++ apply H.
Qed.

Inductive Formula_derive
          {A: Type}
  : Formula A -> Formula A -> Prop :=
| tl_derives_tl
    (x: Formula A)
  : Formula_derive x x
| true_derives_true
  : Formula_derive true true
| false_derives_false
  : Formula_derive false false
| globally_derives_globally
    (prop: Dec A)
  : Formula_derive (globally prop) (globally prop)
| globally_derives_fail
    (prop: Dec A)
  : Formula_derive (globally prop) false
| eventually_derives_eventually
    (prop: Dec A)
  : Formula_derive (eventually prop) (eventually prop)
| eventually_derives_fail
    (prop: Dec A)
  : Formula_derive (eventually prop) true
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
  : Formula_derive (switch before prop after) false.

Arguments tl_derives_tl [_].
Arguments true_derives_true [_].
Arguments false_derives_false [_].
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
           (int: Interp I),
    Formula_derive tl (deriveFormula int p tl).
Proof.
  intros I A p tl int.
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
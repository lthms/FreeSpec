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

Fixpoint runFormula
         {I: Type -> Type}
         {A: Type}
         (int: Interp I)
         (p: Program I A)
         (tl: Formula (ISet I))
  : (A * (Interp I) * Formula (ISet I)) :=
  match p with
  | ret a => (a, int, tl)
  | instr i => (evalInstruction int i,
                execInstruction int i,
                tl_step (instruction i) tl)
  | bind p' f => runFormula (snd (fst (runFormula int p' tl)))
                       (f (fst (fst (runFormula int p' tl))))
                       (snd (runFormula int p' tl))
  end.

Definition evalFormula
           {I: Type -> Type}
           {A: Type}
           (int: Interp I)
           (p: Program I A)
           (tl: Formula (ISet I))
  : A :=
  fst (fst (runFormula int p tl)).

Definition execFormula
           {I: Type -> Type}
           {A: Type}
           (int: Interp I)
           (p: Program I A)
           (tl: Formula (ISet I))
  : Interp I :=
  snd (fst (runFormula int p tl)).

Definition deriveFormula
           {I: Type -> Type}
           {A: Type}
           (int: Interp I)
           (p: Program I A)
           (tl: Formula (ISet I))
  : Formula (ISet I) :=
  snd (runFormula int p tl).

Lemma run_tl_run_program_same
      {I: Type -> Type}
      {A: Type}
  : forall (p: Program I A)
           (tl: Formula (ISet I))
           (int: Interp I),
    fst (runFormula int p tl) = runProgram int p.
Proof.
  induction p; intros tl int; cbn.
  + reflexivity.
  + apply injective_projections; reflexivity.
  + rewrite H; rewrite IHp; reflexivity.
Qed.

Lemma exec_tl_exec_program_same
      {I: Type -> Type}
      {A: Type}
  : forall (p: Program I A)
           (tl: Formula (ISet I))
           (int: Interp I),
    execFormula int p tl = execProgram int p.
Proof.
  intros p tl int.
  unfold execFormula, execProgram.
  rewrite run_tl_run_program_same.
  reflexivity.
Qed.

Lemma eval_tl_eval_program_same
      {I: Type -> Type}
      {A: Type}
  : forall (p: Program I A)
           (tl: Formula (ISet I))
           (int: Interp I),
    evalFormula int p tl = evalProgram int p.
Proof.
  intros p tl int.
  unfold evalFormula, execProgram.
  rewrite run_tl_run_program_same.
  reflexivity.
Qed.

Add Parametric Morphism
    (I: Type -> Type)
    (A: Type)
  : (evalFormula)
    with signature (eq) ==> (@program_eq I A) ==> (eq) ==> (eq)
      as eval_tl_morphism.
Proof.
  intros int p p' Heq tl.
  unfold evalFormula.
  rewrite run_tl_run_program_same.
  rewrite run_tl_run_program_same.
  rewrite Heq.
  reflexivity.
Qed.

Add Parametric Morphism
    (I: Type -> Type)
    (A: Type)
  : (execFormula)
    with signature (eq) ==> (@program_eq I A) ==> (eq) ==> (@interp_eq I)
      as exec_tl_morphism.
Proof.
  intros int p p' Heq tl.
  unfold execFormula.
  rewrite run_tl_run_program_same.
  rewrite run_tl_run_program_same.
  rewrite Heq.
  reflexivity.
Qed.

Lemma run_tl_bind_ret
      {I: Type -> Type}
      {A B: Type}
      (int: Interp I)
      (a: A)
      (f: A -> Program I B)
      (tl: Formula (ISet I))
  : runFormula int (bind (ret a) f) tl = runFormula int (f a) tl.
Proof.
  reflexivity.
Qed.

Lemma exec_tl_bind_ret
      {I: Type -> Type}
      {A B: Type}
      (int: Interp I)
      (a: A)
      (f: A -> Program I B)
      (tl: Formula (ISet I))
  : execFormula int (bind (ret a) f) tl = execFormula int (f a) tl.
Proof.
  reflexivity.
Qed.

Lemma derive_tl_bind_ret
      {I: Type -> Type}
      {A B: Type}
      (int: Interp I)
      (a: A)
      (f: A -> Program I B)
      (tl: Formula (ISet I))
  : deriveFormula int (bind (ret a) f) tl = deriveFormula int (f a) tl.
Proof.
  reflexivity.
Qed.

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

Record FormulaContract
       (I: Type -> Type)
  :=
    { tl_requirements
      : Formula (ISet I)
    ; tl_promises {A: Type}
                  (i: I A)
      : typeret i -> Prop
    }.

Arguments tl_requirements [_].
Arguments tl_promises [_] (_) [_] (_ _).

Definition contract_step
           {I: Type -> Type}
           {A: Type}
           (i: I A)
           (c: FormulaContract I)
  : FormulaContract I :=
  {| tl_requirements := tl_step (instruction i) (tl_requirements c)
   ; tl_promises := fun _ i => tl_promises c i
  |}.

Definition contract_derive
           {I: Type -> Type}
           {A: Type}
           (p: Program I A)
           (int: Interp I)
           (c: FormulaContract I)
  : FormulaContract I :=
  {| tl_requirements := deriveFormula int p (tl_requirements c)
   ; tl_promises := fun _ i => tl_promises c i
  |}.

Lemma contract_derives_ret_eq
      {I: Type -> Type}
      {A: Type}
      (a: A)
      (int: Interp I)
      (c: FormulaContract I)
  : contract_derive (ret a) int c = c.
Proof.
  induction c.
  split.
Qed.

Lemma contract_derives_contract_step
      {I: Type -> Type}
      {A: Type}
      (i: I A)
      (int: Interp I)
      (c: FormulaContract I)
  : contract_derive (instr i) int c = contract_step i c.
Proof.
  unfold contract_derive, contract_step.
  reflexivity.
Qed.

CoInductive FormulaEnforcer
            {I: Type -> Type}
            (int: Interp I)
  : FormulaContract I -> Prop :=
| enforced (c: FormulaContract I)
           (Hprom: forall {A: Type}
                          (i: I A),
               instruction_satisfies (instruction i) (tl_requirements c)
               -> (tl_promises c i) (evalInstruction int i))
           (Henf:  forall {A: Type}
                          (i: I A),
               instruction_satisfies (instruction i) (tl_requirements c)
               -> FormulaEnforcer (execInstruction int i) (contract_step i c))
  : FormulaEnforcer int c.

Lemma enforcer_enforces_promises
      {I: Type -> Type}
      {A: Type}
      (i: I A)
      (int: Interp I)
      (c: FormulaContract I)
      (Henf: FormulaEnforcer int c)
      (Hreq: instruction_satisfies (instruction i) (tl_requirements c))
  : tl_promises c i (evalInstruction int i).
Proof.
  destruct Henf.
  apply Hprom.
  exact Hreq.
Qed.

Inductive tl_contractfull_program
          {I: Type -> Type}
          (c: FormulaContract I)
  : forall {A: Type}, Program I A -> Prop :=
| tl_contractfull_instr {A: Type}
                        (i: I A)
                        (Hreq: instruction_satisfies (instruction i) (tl_requirements c))
  : tl_contractfull_program c (instr i)
| tl_contractfull_ret {A: Type}
                      (a: A)
  : tl_contractfull_program c (ret a)
| tl_contractfull_inv {A B: Type}
                      (p: Program I A)
                      (f: A -> Program I B)
                      (Hcp: tl_contractfull_program c p)
                      (Hnext: forall (int: Interp I)
                                     (Henf: FormulaEnforcer int c),
                          tl_contractfull_program (contract_derive p int c) (f (evalProgram int p)))
  : tl_contractfull_program c (bind p f).

Lemma contractfull_program_bind_ret
      {I: Type -> Type}
      {A B: Type}
      (a: A)
      (f: A -> Program I B)
      (c: FormulaContract I)
  : tl_contractfull_program c (f a) -> tl_contractfull_program c (bind (ret a) f).
Proof.
  intros Hp.
  constructor.
  + constructor.
  + intros int Henf.
    cbn.
    rewrite contract_derives_ret_eq.
    exact Hp.
Qed.

Conjecture contractfull_program_bind_ret'
  : forall {I: Type -> Type}
           {A B: Type}
           (a: A)
           (f: A -> Program I B)
           (c: FormulaContract I),
    tl_contractfull_program c (bind (ret a) f) -> tl_contractfull_program c (f a).

Lemma enforcer_instruction_contractfull_enforcer
      {I: Type -> Type}
      {A: Type}
      (i: I A)
      (int: Interp I)
      (c: FormulaContract I)
      (H: FormulaEnforcer int c)
      (Hp: tl_contractfull_program c (instr i))
  : FormulaEnforcer (execFormula int (instr i) (tl_requirements c)) (contract_derive (instr i) int c).
Proof.
  cbn.
  constructor.
  + intros B i' Hinst.
    destruct H as [c Hprom Henf].
    inversion Hp.
    apply Henf in Hreq.
    apply inj_pair2 in H1.
    subst.
    inversion Hreq.
    rewrite contract_derives_contract_step.
    apply Hprom0.
    exact Hinst.
  + intros B i' Hinst.
    destruct H as [c Hprom Henf].
    inversion Hp.
    apply Henf in Hreq.
    apply inj_pair2 in H1.
    subst.
    inversion Hreq.
    rewrite contract_derives_contract_step.
    apply Henf0.
    exact Hinst.
Qed.

Lemma enforcer_ret_contractfull_enforcer
      {I: Type -> Type}
      {A: Type}
      (a: A)
      (int: Interp I)
      (c: FormulaContract I)
      (H: FormulaEnforcer int c)
  : FormulaEnforcer (execFormula int (ret a) (tl_requirements c)) (contract_derive (ret a) int c).
Proof.
  rewrite (contract_derives_ret_eq a int c).
  unfold execFormula.
  cbn.
  exact H.
Qed.

Lemma contract_derive_assoc
      {I: Type -> Type}
      {A B C: Type}
      (p: Program I A)
      (f: A -> Program I B)
      (f': B -> Program I C)
      (int: Interp I)
      (c: FormulaContract I)
  : contract_derive (bind (bind p f) f') int c
    = contract_derive (bind p (fun x => bind (f x) f')) int c.
Proof.
  reflexivity.
Qed.

Lemma exec_program_assoc'
      (I: Type -> Type)
      {A: Type}
      (p: Program I A)
  : forall {B C: Type}
           (f: A -> Program I B)
           (f': B -> Program I C)
           (int: Interp I),
    execProgram int (bind (bind p f) f')
    = execProgram int (bind p (fun x => (bind (f x) f'))).
Proof.
  intros B C f f' int.
  reflexivity.
Qed.

Lemma exec_tl_assoc
      {I: Type -> Type}
      {A: Type}
      (p: Program I A)
  : forall {B: Type}
           (f: A -> Program I B)
           (int: Interp I)
           (c: FormulaContract I),
    execFormula int (bind p f) (tl_requirements c)
    = execFormula (execFormula int p (tl_requirements c))
             (f (evalProgram int p)) (tl_requirements (contract_derive p int c)).
Proof.
  intros B f int c.
  repeat rewrite exec_tl_exec_program_same.
  reflexivity.
Qed.

Lemma eval_program_assoc
      {I: Type -> Type}
      {A: Type}
      (p: Program I A)
  : forall {B: Type}
           (f: A -> Program I B)
           (int: Interp I)
           (c: FormulaContract I),
    evalProgram int (bind p f)
    = evalProgram (execFormula int p (tl_requirements c))
                  (f (evalProgram int p)).
Proof.
  intros B f int c.
  rewrite exec_tl_exec_program_same.
  reflexivity.
Qed.

Lemma contract_derive_bind
      {I: Type -> Type}
      {A: Type}
      (p: Program I A)
  : forall {B: Type}
           (f: A -> Program I B)
           (int: Interp I)
           (c: FormulaContract I),
    contract_derive (f (evalProgram int p)) (execFormula int p (tl_requirements c)) (contract_derive p int c) = contract_derive (bind p f) int c.
Proof.
  induction p.
  + reflexivity.
  + reflexivity.
  + intros C f' int' c'.
    rewrite contract_derive_assoc.
    rewrite <- (IHp C) .
    rewrite <- H.
    rewrite <- eval_program_assoc.
    rewrite <- exec_tl_assoc.
    rewrite <- (IHp A) .
    reflexivity.
Qed.

Lemma execFormula_bind
      {I: Type -> Type}
      {A B: Type}
      (p: Program I A)
  : forall (f: A -> Program I B)
           (int: Interp I)
           (c: FormulaContract I),
    execFormula (execFormula int p (tl_requirements c)) (f (evalProgram int p)) (tl_requirements (contract_derive p int c)) = execFormula int (bind p f) (tl_requirements c).
Proof.
  intros f int c.
  repeat rewrite exec_tl_exec_program_same.
  reflexivity.
Qed.

Lemma enforcer_contractfull_enforcer
      {I: Type -> Type}
      {A: Type}
      (p: Program I A)
  : forall (c: FormulaContract I)
           (int: Interp I)
           (H: FormulaEnforcer int c)
           (Hp: tl_contractfull_program c p),
    FormulaEnforcer (execFormula int p (tl_requirements c)) (contract_derive p int c).
Proof.
  induction p.
  + intros c int He Hp;
      apply (enforcer_ret_contractfull_enforcer a int c He).
  + intros c int He Hp;
      apply (enforcer_instruction_contractfull_enforcer i int c He Hp).
  + intros c int He Hp.
    inversion Hp;
      apply inj_pair2 in H3;
      repeat apply inj_pair2 in H4;
      subst.
    apply (IHp c int He) in Hcp.
    rewrite <- execFormula_bind.
    rewrite <- contract_derive_bind.
    apply H.
    ++ exact Hcp.
    ++ apply Hnext.
       exact He.
Qed.

Definition tl_contract_preserves_inv
           {I: Type -> Type}
           {State: Type}
           (c: FormulaContract I)
           (inv: Formula (ISet I) -> State -> Prop)
           (step: PS State)
  := forall {A: Type}
            (i: I A)
            (s: State)
            (tl: Formula (ISet I))
            (Hderive: Formula_derive (tl_requirements c) tl),
    inv tl s
    -> instruction_satisfies (instruction i) tl
    -> inv (tl_step (instruction i) tl) (snd (step A s i)).

Lemma tl_contract_preserves_inv_propagates
      {I: Type -> Type}
      {State: Type}
      (c: FormulaContract I)
      (inv: Formula (ISet I) -> State -> Prop)
      (step: PS State)
  : forall {A: Type}
           (i: I A),
    tl_contract_preserves_inv c inv step
    -> instruction_satisfies (instruction i) (tl_requirements c)
    -> tl_contract_preserves_inv (contract_step i c) inv step.
Proof.
  intros A i Hpres Hreq.
  unfold tl_contract_preserves_inv in *.
  intros B i' s tl Hderive Hinv Hreq'.
  apply Hpres.
  + apply tl_derive_trans with (tl':=tl_requirements (contract_step i c)).
    ++ cbn.
       apply tl_step_is_tl_derive.
       apply Formula_step_is_tl_step.
    ++ exact Hderive.
  + exact Hinv.
  + exact Hreq'.
Qed.

Definition tl_contract_enforces_promises
           {I: Type -> Type}
           {State: Type}
           (c: FormulaContract I)
           (inv: Formula (ISet I) -> State -> Prop)
           (step: PS State)
  := forall {A: Type}
            (i: I A)
            (s: State)
            (tl: Formula (ISet I))
            (Hderive: Formula_derive (tl_requirements c) tl),
    inv tl s
    -> instruction_satisfies (instruction i) tl
    -> tl_promises c i (fst (step A s i)).

Lemma tl_contract_enforces_promises_propagates
      {I: Type -> Type}
      {State: Type}
      (c: FormulaContract I)
      (inv: Formula (ISet I) -> State -> Prop)
      (step: PS State)
  : forall {A: Type}
           (i: I A),
    tl_contract_enforces_promises c inv step
    -> instruction_satisfies (instruction i) (tl_requirements c)
    -> tl_contract_enforces_promises (contract_step i c) inv step.
Proof.
  intros A i Henf Hreq.
  unfold tl_contract_enforces_promises in *.
  intros B i' s tl Hderive Hinv Hreq'.
  cbn.
  apply Henf with (tl:=tl).
  + apply tl_derive_trans with (tl':=tl_requirements (contract_step i c)).
    ++ cbn.
       apply tl_step_is_tl_derive.
       apply Formula_step_is_tl_step.
    ++ exact Hderive.
  + exact Hinv.
  + exact Hreq'.
Qed.

Fact _stateful_contract_enforcement
     {I: Type -> Type}
     {State: Type}
     (c: FormulaContract I)
     (inv: Formula (ISet I) -> State -> Prop)
     (step: PS State)
  : forall (c': FormulaContract I)
           (Hpres: tl_contract_preserves_inv c' inv step)
           (Henf: tl_contract_enforces_promises c' inv step)
           (s: State),
    tl_promises c = tl_promises c'
    -> Formula_derive (tl_requirements c) (tl_requirements c')
    -> inv (tl_requirements c') s
    -> FormulaEnforcer (mkInterp step s) c'.
Proof.
  cofix.
  intros c' Hpres Henf s Hprom_eq Hderive Hinv .
  assert (Formula_derive (tl_requirements c') (tl_requirements c'))
    as Hderive'
      by (apply tl_derives_tl).
  constructor.
  + intros A i Hreq.
    unfold tl_contract_enforces_promises in Henf.
    cbn.
    apply (Henf A i s (tl_requirements c') Hderive' Hinv Hreq).
  + intros A i Hreq.
    apply _stateful_contract_enforcement.
    ++ apply tl_contract_preserves_inv_propagates.
       +++ exact Hpres.
       +++ exact Hreq.
    ++ apply tl_contract_enforces_promises_propagates.
       +++ exact Henf.
       +++ exact Hreq.
    ++ rewrite Hprom_eq.
       reflexivity.
    ++ unfold contract_step.
       cbn.
       apply tl_derive_trans with (tl':=tl_requirements c').
       +++ exact Hderive.
       +++ apply tl_step_is_tl_derive.
           apply Formula_step_is_tl_step.
    ++ unfold tl_contract_preserves_inv in Hpres.
       cbn.
       apply (Hpres A i s (tl_requirements c')).
       +++ apply tl_derives_tl.
       +++ exact Hinv.
       +++ exact Hreq.
Qed.

Lemma tl_stateful_contract_enforcement
      {I: Type -> Type}
      {State: Type}
      (c: FormulaContract I)
      (inv: Formula (ISet I) -> State -> Prop)
      (step: PS State)
      (Hpres: tl_contract_preserves_inv c inv step)
      (Henf: tl_contract_enforces_promises c inv step)
  : forall (s: State),
    inv (tl_requirements c) s
    -> FormulaEnforcer (mkInterp step s) c.
Proof.
  intros s Hinv.
  assert (tl_promises c = tl_promises c)
    as Heq
      by reflexivity.
  assert (Formula_derive (tl_requirements c) (tl_requirements c))
    as Hderive
      by (apply tl_derives_tl).
  apply (_stateful_contract_enforcement c inv step c Hpres Henf s Heq Hderive Hinv).
Qed.
Require Import Coq.Program.Equality.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Logic.Classical.
Require Import Coq.Setoids.Setoid.

Require Import FreeSpec.Utils.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Program.
Require Import FreeSpec.Equiv.

Record Instant
       (A: Type) :=
  { prop: A -> Prop
  ; prop_dec: forall (a: A), {prop a}+{~prop a}
  }.

Arguments prop [A] (_ _).
Arguments prop_dec [A] (_ _).

Notation "p ? a" := (prop_dec p a) (at level 51): instant_scope.
Notation "p .? a" := (prop p a) (at level 51): instant_scope.

Local Open Scope instant_scope.
Local Open Scope eq_scope.

Inductive TL
          (A: Type)
  : Type :=
| true
  : TL A
| false
  : TL A
| globally (prop: Instant A)
  : TL A
| eventually (prop: Instant A)
  : TL A
| next (tl: TL A)
  : TL A
| switch (tl1: TL A)
         (prop: Instant A)
         (tl2: TL A)
  : TL A.

Arguments true [_].
Arguments false [_].
Arguments globally [_] (_).
Arguments eventually [_] (_).
Arguments next [_] (_).
Arguments switch [_] (_ _ _).

Fixpoint halt_satisfies
         {A: Type}
         (tl: TL A)
  : Prop :=
  match tl with
  | eventually _ => False
  | next _ => False
  | switch before _ _ => halt_satisfies before
  | _ => True
  end.

Fixpoint halt_satisfies_dec
         {A: Type}
         (tl: TL A)
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

Inductive TL_step
          {A: Type}
  : TL A -> TL A -> Prop :=
| true_stays_true: TL_step true true
| false_stays_false: TL_step false false
| globally_stays_globally
    (prop: Instant A)
  : TL_step (globally prop) (globally prop)
| globally_can_fail
    (prop: Instant A)
  : TL_step (globally prop) false
| eventually_stays_eventually
    (prop: Instant A)
  : TL_step (eventually prop) (eventually prop)
| eventually_can_succeed
    (prop: Instant A)
  : TL_step (eventually prop) true
| next_steps_unwrap
    (tl: TL A)
  : TL_step (next tl) tl
| switch_steps_before
    (tl1 tl2 tl3: TL A)
    (prop: Instant A)
    (Hderive: TL_step tl1 tl2)
  : TL_step (switch tl1 prop tl3) (switch tl2 prop tl3)
| switch_step_after_small
    (tl1 tl2: TL A)
    (prop: Instant A)
  : TL_step (switch tl1 prop tl2) tl2
| switch_can_fail
    (tl1 tl2: TL A)
    (prop: Instant A)
  : TL_step (switch tl1 prop tl2) false.

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
         (tl: TL A)
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
         (tl: TL A)
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
         (tl: TL A)
  : TL A :=
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

Lemma TL_step_is_tl_step
      {A: Type}
      (a: A)
      (tl: TL A)
  : TL_step tl (tl_step a tl).
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

Fixpoint runTL
         {I: Type -> Type}
         {A: Type}
         (int: Interp I)
         (p: Program I A)
         (tl: TL (ISet I))
  : (A * (Interp I) * TL (ISet I)) :=
  match p with
  | ret a => (a, int, tl)
  | instr i => (evalInstruction int i,
                execInstruction int i,
                tl_step (instruction i) tl)
  | bind p' f => runTL (snd (fst (runTL int p' tl)))
                       (f (fst (fst (runTL int p' tl))))
                       (snd (runTL int p' tl))
  end.

Definition evalTL
           {I: Type -> Type}
           {A: Type}
           (int: Interp I)
           (p: Program I A)
           (tl: TL (ISet I))
  : A :=
  fst (fst (runTL int p tl)).

Definition execTL
           {I: Type -> Type}
           {A: Type}
           (int: Interp I)
           (p: Program I A)
           (tl: TL (ISet I))
  : Interp I :=
  snd (fst (runTL int p tl)).

Definition deriveTL
           {I: Type -> Type}
           {A: Type}
           (int: Interp I)
           (p: Program I A)
           (tl: TL (ISet I))
  : TL (ISet I) :=
  snd (runTL int p tl).

Lemma run_tl_run_program_same
      {I: Type -> Type}
      {A: Type}
  : forall (p: Program I A)
           (tl: TL (ISet I))
           (int: Interp I),
    fst (runTL int p tl) = runProgram int p.
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
           (tl: TL (ISet I))
           (int: Interp I),
    execTL int p tl = execProgram int p.
Proof.
  intros p tl int.
  unfold execTL, execProgram.
  rewrite run_tl_run_program_same.
  reflexivity.
Qed.

Lemma eval_tl_eval_program_same
      {I: Type -> Type}
      {A: Type}
  : forall (p: Program I A)
           (tl: TL (ISet I))
           (int: Interp I),
    evalTL int p tl = evalProgram int p.
Proof.
  intros p tl int.
  unfold evalTL, execProgram.
  rewrite run_tl_run_program_same.
  reflexivity.
Qed.

Add Parametric Morphism
    (I: Type -> Type)
    (A: Type)
  : (evalTL)
    with signature (eq) ==> (@program_eq I A) ==> (eq) ==> (eq)
      as eval_tl_morphism.
Proof.
  intros int p p' Heq tl.
  unfold evalTL.
  rewrite run_tl_run_program_same.
  rewrite run_tl_run_program_same.
  rewrite Heq.
  reflexivity.
Qed.

Add Parametric Morphism
    (I: Type -> Type)
    (A: Type)
  : (execTL)
    with signature (eq) ==> (@program_eq I A) ==> (eq) ==> (@interp_eq I)
      as exec_tl_morphism.
Proof.
  intros int p p' Heq tl.
  unfold execTL.
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
      (tl: TL (ISet I))
  : runTL int (bind (ret a) f) tl = runTL int (f a) tl.
Proof.
  reflexivity.
Qed.

Lemma exec_tl_bind_ret
      {I: Type -> Type}
      {A B: Type}
      (int: Interp I)
      (a: A)
      (f: A -> Program I B)
      (tl: TL (ISet I))
  : execTL int (bind (ret a) f) tl = execTL int (f a) tl.
Proof.
  reflexivity.
Qed.

Lemma derive_tl_bind_ret
      {I: Type -> Type}
      {A B: Type}
      (int: Interp I)
      (a: A)
      (f: A -> Program I B)
      (tl: TL (ISet I))
  : deriveTL int (bind (ret a) f) tl = deriveTL int (f a) tl.
Proof.
  reflexivity.
Qed.

Inductive TL_run
          {A: Type}
  : TL A -> TL A -> Prop :=
| tl_run_refl
    (tl: TL A)
  : TL_run tl tl
| tl_run_small_step
    (from to: TL A)
    (Hstep: TL_step from to)
  : TL_run from to
| tl_run_big_step
    (from tl to: TL A)
    (Hstep: TL_step from tl)
    (Hrun: TL_run tl to)
  : TL_run from to.

Lemma tl_step_run_trans
      {A: Type}
      (tl tl' tl'': TL A)
  : TL_step tl tl'
    -> TL_step tl' tl''
    -> TL_run tl tl''.
Proof.
  intros H1 H2.
  apply (tl_run_big_step tl tl' tl'').
  + exact H1.
  + apply (tl_run_small_step tl' tl'' H2).
Qed.

Lemma tl_run_step_run
      {A: Type}
      (tl tl' tl'': TL A)
  : TL_run tl tl'
    -> TL_step tl' tl''
    -> TL_run tl tl''.
Proof.
  intros H1 H2.
  induction H1.
  ++ constructor.
     exact H2.
  ++ apply (tl_step_run_trans from to tl'' Hstep H2).
  ++ apply IHTL_run in H2.
     apply (tl_run_big_step from tl tl'' Hstep H2).
Qed.

Lemma tl_run_trans
      {A: Type}
      (tl tl' tl'': TL A)
  : TL_run tl tl'
    -> TL_run tl' tl''
    -> TL_run tl tl''.
Proof.
  intros H1 H2.
  induction H1.
  + exact H2.
  + apply (tl_run_big_step from to tl'' Hstep H2).
  + apply IHTL_run in H2.
    apply (tl_run_big_step from tl tl'' Hstep H2).
Qed.

Lemma next_derives_big
      {A: Type}
      (tl tl': TL A)
      (Hderive: TL_run tl tl')
  : TL_run (next tl) tl'.
Proof.
  assert (TL_run (next tl) tl)
    as Hbefore
      by (repeat constructor).
  apply (tl_run_trans (next tl) tl tl' Hbefore Hderive).
Qed.

Lemma switch_derives_after_big
      {A: Type}
      (tl1 tl2 tl3: TL A)
      (prop: Instant A)
      (Hderive: TL_run tl2 tl3)
  : TL_run (switch tl1 prop tl2) tl3.
Proof.
  assert (TL_run (switch tl1 prop tl2) tl2)
    as Hrun'
      by (repeat constructor).
  apply (tl_run_trans (switch tl1 prop tl2) tl2 tl3 Hrun' Hderive).
Qed.

Lemma switch_derives_before_big
      {A: Type}
      (tl1 tl2 tl3: TL A)
      (prop: Instant A)
      (Hderive: TL_run tl1 tl2)
  : TL_run (switch tl1 prop tl3) (switch tl2 prop tl3).
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

Lemma TL_run_is_runTL
  : forall {I: Type -> Type}
           {A: Type}
           (p: Program I A)
           (tl: TL (ISet I))
           (int: Interp I),
    TL_run tl (deriveTL int p tl).
Proof.
  induction p.
  + intros tl int.
    cbn.
    apply tl_run_refl.
  + intros tl int.
    cbn.
    constructor.
    apply TL_step_is_tl_step.
  + intros tl int.
    cbn.
    apply (tl_run_trans tl
                        (snd (runTL int p tl))
                        (snd
                           (runTL (snd (fst (runTL int p tl))) (f (fst (fst (runTL int p tl))))
                                  (snd (runTL int p tl))))).
    ++ apply IHp.
    ++ apply H.
Qed.

Inductive TL_derive
          {A: Type}
  : TL A -> TL A -> Prop :=
| tl_derives_tl
    (x: TL A)
  : TL_derive x x
| true_derives_true
  : TL_derive true true
| false_derives_false
  : TL_derive false false
| globally_derives_globally
    (prop: Instant A)
  : TL_derive (globally prop) (globally prop)
| globally_derives_fail
    (prop: Instant A)
  : TL_derive (globally prop) false
| eventually_derives_eventually
    (prop: Instant A)
  : TL_derive (eventually prop) (eventually prop)
| eventually_derives_fail
    (prop: Instant A)
  : TL_derive (eventually prop) true
| next_derives_unwrap
    (tl tl': TL A)
    (Hderive: TL_derive tl tl')
  : TL_derive (next tl) tl'
| switch_derives_before
    (before after tl: TL A)
    (prop: Instant A)
    (Hderive: TL_derive before tl)
  : TL_derive (switch before prop after) (switch tl prop after)
| switch_derives_after
    (before after tl: TL A)
    (prop: Instant A)
    (Hderive: TL_derive after tl)
  : TL_derive (switch before prop after) tl
| switch_derives_fail
    (before after: TL A)
    (prop: Instant A)
  : TL_derive (switch before prop after) false.

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
  : forall (tl tl': TL A),
    TL_step  tl tl' -> TL_derive tl tl'.
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
  : forall (tl tl': TL A),
    TL_derive tl tl' -> TL_run  tl tl'.
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
    ++ assert (TL_run (next tl) tl)
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
      (tl1 tl2 tl3: TL A)
      (prop: Instant A)
      (Hderive: TL_derive tl1 tl2)
  : TL_derive (switch tl1 prop tl3) (switch tl2 prop tl3).
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
  : forall (tl tl': TL A),
    TL_derive tl tl' -> (forall (tl'': TL A), TL_derive tl' tl'' -> TL_derive tl tl'').
Proof.
  intros tl tl' H1; induction H1; intros tl'' H2; try exact H2.
  + inversion_clear H2;
      constructor.
  + inversion_clear H2;
      constructor.
  + constructor.
    apply (IHTL_derive tl'' H2).
  + inversion_clear H2.
    ++ apply switch_derives_before_helper.
       exact H1.
    ++ apply switch_derives_before_helper.
       apply (IHTL_derive tl0 Hderive).
    ++ apply switch_derives_after.
       exact Hderive.
    ++ apply switch_derives_fail.
  + apply switch_derives_after.
    apply IHTL_derive in H2.
    exact H2.
  + inversion_clear H2.
    ++ apply switch_derives_fail.
    ++ apply switch_derives_fail.
Qed.

Lemma tl_derive_trans
      {A: Type}
  : forall (tl tl' tl'': TL A),
    TL_derive tl tl' -> TL_derive tl' tl'' -> TL_derive tl tl''.
Proof.
  intros tl tl' tl'' H1 H2.
  apply (tl_derive_trans' tl tl' H1 tl'' H2).
Qed.

Lemma tl_derive_implies_tl_run
      {A: Type}
  : forall (tl tl': TL A),
    TL_run tl tl' -> TL_derive  tl tl'.
Proof.
  intros.
  induction H.
  + constructor.
  + apply tl_step_is_tl_derive in Hstep.
    exact Hstep.
  + apply tl_step_is_tl_derive in Hstep.
    apply (tl_derive_trans from tl to Hstep IHTL_run).
Qed.

Theorem derive_is_run_and_run_is_derive
        {A: Type}
        (tl tl': TL A)
  : TL_run tl tl' <-> TL_derive tl tl'.
Proof.
  split.
  + apply tl_derive_implies_tl_run.
  + apply tl_run_implies_tl_derive.
Qed.

Corollary TL_derive_is_runTL
  : forall {I: Type -> Type}
           {A: Type}
           (p: Program I A)
           (tl: TL (ISet I))
           (int: Interp I),
    TL_derive tl (deriveTL int p tl).
Proof.
  intros I A p tl int.
  apply tl_derive_implies_tl_run.
  apply TL_run_is_runTL.
Qed.

Lemma tl_run_switch_before
      {A: Type}
  : forall (tl tl' tl2: TL A)
           (prop: Instant A),
    TL_run tl tl'
    -> TL_run (switch tl prop tl2) (switch tl' prop tl2).
Proof.
  intros tl tl' tl2 prop Hrun.
  apply tl_run_implies_tl_derive.
  apply tl_derive_implies_tl_run in Hrun.
  apply switch_derives_before.
  exact Hrun.
Qed.

Record TLContract
       (I: Type -> Type)
  :=
    { tl_requirements
      : TL (ISet I)
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
           (c: TLContract I)
  : TLContract I :=
  {| tl_requirements := tl_step (instruction i) (tl_requirements c)
   ; tl_promises := fun _ i => tl_promises c i
  |}.

Definition contract_derive
           {I: Type -> Type}
           {A: Type}
           (p: Program I A)
           (int: Interp I)
           (c: TLContract I)
  : TLContract I :=
  {| tl_requirements := deriveTL int p (tl_requirements c)
   ; tl_promises := fun _ i => tl_promises c i
  |}.

Lemma contract_derives_ret_eq
      {I: Type -> Type}
      {A: Type}
      (a: A)
      (int: Interp I)
      (c: TLContract I)
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
      (c: TLContract I)
  : contract_derive (instr i) int c = contract_step i c.
Proof.
  unfold contract_derive, contract_step.
  reflexivity.
Qed.

CoInductive TLEnforcer
            {I: Type -> Type}
            (int: Interp I)
  : TLContract I -> Prop :=
| enforced (c: TLContract I)
           (Hprom: forall {A: Type}
                          (i: I A),
               instruction_satisfies (instruction i) (tl_requirements c)
               -> (tl_promises c i) (evalInstruction int i))
           (Henf:  forall {A: Type}
                          (i: I A),
               instruction_satisfies (instruction i) (tl_requirements c)
               -> TLEnforcer (execInstruction int i) (contract_step i c))
  : TLEnforcer int c.

Lemma enforcer_enforces_promises
      {I: Type -> Type}
      {A: Type}
      (i: I A)
      (int: Interp I)
      (c: TLContract I)
      (Henf: TLEnforcer int c)
      (Hreq: instruction_satisfies (instruction i) (tl_requirements c))
  : tl_promises c i (evalInstruction int i).
Proof.
  destruct Henf.
  apply Hprom.
  exact Hreq.
Qed.

Inductive tl_contractfull_program
          {I: Type -> Type}
          (c: TLContract I)
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
                                     (Henf: TLEnforcer int c),
                          tl_contractfull_program (contract_derive p int c) (f (evalProgram int p)))
  : tl_contractfull_program c (bind p f).

Lemma contractfull_program_bind_ret
      {I: Type -> Type}
      {A B: Type}
      (a: A)
      (f: A -> Program I B)
      (c: TLContract I)
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
           (c: TLContract I),
    tl_contractfull_program c (bind (ret a) f) -> tl_contractfull_program c (f a).

Lemma enforcer_instruction_contractfull_enforcer
      {I: Type -> Type}
      {A: Type}
      (i: I A)
      (int: Interp I)
      (c: TLContract I)
      (H: TLEnforcer int c)
      (Hp: tl_contractfull_program c (instr i))
  : TLEnforcer (execTL int (instr i) (tl_requirements c)) (contract_derive (instr i) int c).
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
      (c: TLContract I)
      (H: TLEnforcer int c)
  : TLEnforcer (execTL int (ret a) (tl_requirements c)) (contract_derive (ret a) int c).
Proof.
  rewrite (contract_derives_ret_eq a int c).
  unfold execTL.
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
      (c: TLContract I)
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
           (c: TLContract I),
    execTL int (bind p f) (tl_requirements c)
    = execTL (execTL int p (tl_requirements c))
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
           (c: TLContract I),
    evalProgram int (bind p f)
    = evalProgram (execTL int p (tl_requirements c))
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
           (c: TLContract I),
    contract_derive (f (evalProgram int p)) (execTL int p (tl_requirements c)) (contract_derive p int c) = contract_derive (bind p f) int c.
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

Lemma execTL_bind
      {I: Type -> Type}
      {A B: Type}
      (p: Program I A)
  : forall (f: A -> Program I B)
           (int: Interp I)
           (c: TLContract I),
    execTL (execTL int p (tl_requirements c)) (f (evalProgram int p)) (tl_requirements (contract_derive p int c)) = execTL int (bind p f) (tl_requirements c).
Proof.
  intros f int c.
  repeat rewrite exec_tl_exec_program_same.
  reflexivity.
Qed.

Lemma enforcer_contractfull_enforcer
      {I: Type -> Type}
      {A: Type}
      (p: Program I A)
  : forall (c: TLContract I)
           (int: Interp I)
           (H: TLEnforcer int c)
           (Hp: tl_contractfull_program c p),
    TLEnforcer (execTL int p (tl_requirements c)) (contract_derive p int c).
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
    rewrite <- execTL_bind.
    rewrite <- contract_derive_bind.
    apply H.
    ++ exact Hcp.
    ++ apply Hnext.
       exact He.
Qed.

Definition tl_contract_preserves_inv
           {I: Type -> Type}
           {State: Type}
           (c: TLContract I)
           (inv: TL (ISet I) -> State -> Prop)
           (step: PS State)
  := forall {A: Type}
            (i: I A)
            (s: State)
            (tl: TL (ISet I))
            (Hderive: TL_derive (tl_requirements c) tl),
    inv tl s
    -> instruction_satisfies (instruction i) tl
    -> inv (tl_step (instruction i) tl) (snd (step A s i)).

Lemma tl_contract_preserves_inv_propagates
      {I: Type -> Type}
      {State: Type}
      (c: TLContract I)
      (inv: TL (ISet I) -> State -> Prop)
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
       apply TL_step_is_tl_step.
    ++ exact Hderive.
  + exact Hinv.
  + exact Hreq'.
Qed.

Definition tl_contract_enforces_promises
           {I: Type -> Type}
           {State: Type}
           (c: TLContract I)
           (inv: TL (ISet I) -> State -> Prop)
           (step: PS State)
  := forall {A: Type}
            (i: I A)
            (s: State)
            (tl: TL (ISet I))
            (Hderive: TL_derive (tl_requirements c) tl),
    inv tl s
    -> instruction_satisfies (instruction i) tl
    -> tl_promises c i (fst (step A s i)).

Lemma tl_contract_enforces_promises_propagates
      {I: Type -> Type}
      {State: Type}
      (c: TLContract I)
      (inv: TL (ISet I) -> State -> Prop)
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
       apply TL_step_is_tl_step.
    ++ exact Hderive.
  + exact Hinv.
  + exact Hreq'.
Qed.

Fact _stateful_contract_enforcement
     {I: Type -> Type}
     {State: Type}
     (c: TLContract I)
     (inv: TL (ISet I) -> State -> Prop)
     (step: PS State)
  : forall (c': TLContract I)
           (Hpres: tl_contract_preserves_inv c' inv step)
           (Henf: tl_contract_enforces_promises c' inv step)
           (s: State),
    tl_promises c = tl_promises c'
    -> TL_derive (tl_requirements c) (tl_requirements c')
    -> inv (tl_requirements c') s
    -> TLEnforcer (mkInterp step s) c'.
Proof.
  cofix.
  intros c' Hpres Henf s Hprom_eq Hderive Hinv .
  assert (TL_derive (tl_requirements c') (tl_requirements c'))
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
           apply TL_step_is_tl_step.
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
      (c: TLContract I)
      (inv: TL (ISet I) -> State -> Prop)
      (step: PS State)
      (Hpres: tl_contract_preserves_inv c inv step)
      (Henf: tl_contract_enforces_promises c inv step)
  : forall (s: State),
    inv (tl_requirements c) s
    -> TLEnforcer (mkInterp step s) c.
Proof.
  intros s Hinv.
  assert (tl_promises c = tl_promises c)
    as Heq
      by reflexivity.
  assert (TL_derive (tl_requirements c) (tl_requirements c))
    as Hderive
      by (apply tl_derives_tl).
  apply (_stateful_contract_enforcement c inv step c Hpres Henf s Heq Hderive Hinv).
Qed.
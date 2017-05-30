Require Import Coq.Bool.Sumbool.
Require Import Coq.Logic.Classical.
Require Import FreeSpec.Utils.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Program.

Section TEMPORAL_LOGIC.
  Variables (A: Type)
            (I: Type -> Type).

  Record Instant :=
    { prop: A -> Prop
    ; prop_dec: forall (a: A), {prop a}+{~prop a}
    }.

  Notation "p ? a" := (prop_dec p a) (at level 51).
  Notation "p .? a" := (prop p a) (at level 51).

  Inductive TL: Type :=
  | true
    : TL
  | false
    : TL
  | globally (prop: Instant)
    : TL
  | eventually (prop: Instant)
    : TL
  | next (tl: TL)
    : TL
  | switch (tl1: TL)
           (prop: Instant)
           (tl2: TL)
    : TL.

  Fixpoint halt_satisfies
             (tl: TL)
    : Prop :=
    match tl with
    | eventually _ => False
    | next _ => False
    | switch before _ _ => halt_satisfies before
    | _ => True
    end.

  Fixpoint halt_satisfies_dec
          (tl: TL)
    : {halt_satisfies tl}+{~halt_satisfies tl}.
    refine (
        match tl with
        | eventually _ => false_dec
        | next _ => false_dec
        | switch before _ _ => decide_dec (halt_satisfies_dec before)
        | _ => true_dec
        end);
      cbn;
      firstorder.
    Defined.

  Inductive TL_step
    : TL -> TL -> Prop :=
  | true_stays_true: TL_step true true
  | false_stays_false: TL_step false false
  | globally_stays_globally
      (prop: Instant)
    : TL_step (globally prop) (globally prop)
  | globally_can_fail
      (prop: Instant)
    : TL_step (globally prop) false
  | eventually_stays_eventually
      (prop: Instant)
    : TL_step (eventually prop) (eventually prop)
  | eventually_can_succeed
      (prop: Instant)
    : TL_step (eventually prop) true
  | next_steps_unwrap
      (tl: TL)
    : TL_step (next tl) tl
  | switch_steps_before
      (tl1 tl2 tl3: TL)
      (prop: Instant)
      (Hderive: TL_step tl1 tl2)
    : TL_step (switch tl1 prop tl3) (switch tl2 prop tl3)
  | switch_step_after_small
      (tl1 tl2: TL)
      (prop: Instant)
    : TL_step (switch tl1 prop tl2) tl2
  | switch_can_fail
      (tl1 tl2: TL)
      (prop: Instant)
    : TL_step (switch tl1 prop tl2) false.

  Fixpoint instruction_satisfies
           (a: A)
           (tl: TL)
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
          (a: A)
          (tl: TL)
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
                                          (instruction_satisfies_dec a after)
                                          (halt_satisfies_dec before))
             else decide_dec (instruction_satisfies_dec a before)
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
           (a: A)
           (tl: TL)
    : TL :=
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
    : forall (a: A)
             (tl: TL),
      TL_step tl (tl_step a tl).
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

End TEMPORAL_LOGIC.

Arguments true [_].
Arguments false [_].
Arguments next [_].
Arguments globally [_].
Arguments eventually [_].
Arguments switch [_].

Arguments TL_step [_].
Arguments tl_step [_].

Section RUN_TL.
  Variable (I: Type -> Type).

  Inductive ISet: Type :=
  | instruction {A: Type}
                (i: I A)
    : ISet.

  Fixpoint runTL
           {A: Type}
           (int: Interp I)
           (p: Program I A)
           (tl: TL (ISet))
    : (A * (Interp I) * TL (ISet)) :=
    match p with
    | ret a => (a, int, tl)
    | instr i => (evalInstruction i int,
                    execInstruction i int,
                    tl_step (instruction i) tl)
    | bind p' f => runTL (snd (fst (runTL int p' tl)))
                         (f (fst (fst (runTL int p' tl))))
                         (snd (runTL int p' tl))
    end.

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
        (tl1 tl2 tl3: TL ISet)
        (prop: Instant ISet)
        (Hderive: TL_run tl2 tl3)
    : TL_run (switch tl1 prop tl2) tl3.
  Proof.
    assert (TL_run (switch tl1 prop tl2) tl2)
      as Hrun'
        by (repeat constructor).
    apply (tl_run_trans (switch tl1 prop tl2) tl2 tl3 Hrun' Hderive).
  Qed.

  Lemma switch_derives_before_big
        (tl1 tl2 tl3: TL ISet)
        (prop: Instant ISet)
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
    : forall {A: Type}
             (p: Program I A)
             (tl: TL ISet)
             (int: Interp I),
      TL_run tl (snd (runTL int p tl)).
  Proof.
    induction p.
    + intros tl int.
      cbn.
      apply (tl_run_trans tl
                          (snd (runTL int p tl))
                          (snd
                             (runTL (snd (fst (runTL int p tl))) (f (fst (fst (runTL int p tl))))
                                    (snd (runTL int p tl))))).
      ++ apply IHp.
      ++ apply H.
    + intros tl int.
      cbn.
      constructor.
      apply TL_step_is_tl_step.
    + intros tl int.
      cbn.
      apply tl_run_refl.
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

  Lemma tl_run_switch_before
        {A: Type}
  : forall (tl tl' tl2: TL A)
           (prop: Instant A),
      TL_run tl tl'
      -> TL_run (switch tl prop tl2) (switch tl' prop tl2).
  Proof.
    induction tl.
    + intros.
      assert (tl' = true) as Heqt.
  Admitted.

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
      ++
  Admitted.

  Lemma run_tl_run_program_interp_eq
        {A: Type}
    : forall (p: Program I A)
             (tl: TL (ISet))
             (int: Interp I),
      interp_eq (snd (fst (runTL int p tl))) (execProgram p int).
  Proof.
    cofix.
    induction p.
    + admit.
    + cbn.
      intros tl int.
  Admitted.
End RUN_TL.
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
  | loop (gold: TL)
         (current: TL)
    : TL
  | next (tl: TL)
    : TL
  | switch (tl1: TL)
           (prop: Instant)
           (tl2: TL)
    : TL
  | globally (prop: Instant)
    : TL
  | eventually (prop: Instant)
    : TL
  | true
    : TL
  | false
    : TL.

  Fixpoint halt_satisfies
             (tl: TL)
    : Prop :=
    match tl with
    | loop _ current => halt_satisfies current
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
        | loop _ current => decide_dec (halt_satisfies_dec current)
        | eventually _ => false_dec
        | next _ => false_dec
        | switch before _ _ => decide_dec (halt_satisfies_dec before)
        | _ => true_dec
        end);
      cbn;
      firstorder.
    Defined.

  Fixpoint instruction_satisfies
           (a: A)
           (tl: TL)
    : Prop :=
    match tl with
    | loop _ current
      => instruction_satisfies a current
    | next _
      => True
    | switch before prop after
      => (prop.? a -> instruction_satisfies a after
                      /\ halt_satisfies before)
         /\ (~prop.? a -> instruction_satisfies a before)
    | globally prop => prop.? a
    | eventually tl => True
    | true => True
    | false => False
    end.

  Fixpoint instruction_satisfies_dec
          (a: A)
          (tl: TL)
    : {instruction_satisfies a tl}+{~instruction_satisfies a tl}.
    refine (
        match tl with
        | loop _ current
          => decide_dec (instruction_satisfies_dec a current)
        | next _
          => true_dec
        | globally prop
          => decide_dec (prop? a)
        | switch before p after
          => if p? a
             then decide_dec (sumbool_and _ _ _ _
                                          (instruction_satisfies_dec a after)
                                          (halt_satisfies_dec before))
             else decide_dec (instruction_satisfies_dec a before)
        | eventually prop
          => true_dec
        | true
          => true_dec
        | false
          => false_dec
        end
      ); cbn; trivial.
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
    + intro False; destruct False.
  Defined.

  Fixpoint tl_step
           (a: A)
           (tl: TL)
    : TL :=
    if instruction_satisfies_dec a tl
    then match tl with
         | loop gold current
           => match (tl_step a current) with
              | true => loop gold gold
              | false => false
              | c' => loop gold c'
              end
         | next tl
           => tl
         | switch before p after
           => if p? a
              then after
              else switch before p after
         | eventually p
           => if p ? a
              then true
              else eventually p
         | x
           => x
         end
    else false.
End TEMPORAL_LOGIC.

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
                    tl_step _ (instruction i) tl)
    | bind p' f => runTL (snd (fst (runTL int p' tl)))
                           (f (fst (fst (runTL int p' tl))))
                           (snd (runTL int p' tl))
    end.

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
Require Import FreeSpec.Program.
Require Import FreeSpec.Interp.

(** In this library, we provide an alternative to [runProgram] we can
    use to derive a so-called abstract state through the executed
    primitives of the underlying [Interface]. Using this feature, we
    can verify some properties of a given [Program] _without modifying
    it_.

 *)

(** * Abstract Run

 *)

Fixpoint abstractRun
         {S:        Type}
         {I:        Type -> Type}
         {A:        Type}
         (abs:      S)
         (abs_step: forall (R:Type), I R -> R -> S -> S)
         (int:      Interp I)
         (p:        Program I A)
  : (A * (Interp I) * S) :=
  match p with
  | ret a
    => (a, int, abs)
  | instr i
    => (evalInstruction int i,
        execInstruction int i,
        abs_step _ i (evalInstruction int i) abs)
  | bind p' f
    => abstractRun (snd (abstractRun abs abs_step int p'))
                   abs_step
                   (snd (fst (abstractRun abs abs_step int p')))
                   (f (fst (fst (abstractRun abs abs_step int p' ))))
  end.

(** Similary to [FreeSpec.Program.runProgram], we define several
    helpers functions to select one element among the three that are
    returned by [abstractRun].

 *)

Definition abstractExec
           {S:        Type}
           {I:        Type -> Type}
           {A:        Type}
           (abs:      S)
           (abs_step: forall (R:Type), I R -> R -> S -> S)
           (int:      Interp I)
           (p:        Program I A)
  : Interp I :=
  snd (fst (abstractRun abs abs_step int p)).

Definition abstractEval
           {S:        Type}
           {I:        Type -> Type}
           {A:        Type}
           (abs:      S)
           (abs_step: forall (R:Type), I R -> R -> S -> S)
           (int:      Interp I)
           (p:        Program I A)
  : A :=
  fst (fst (abstractRun abs abs_step int p)).

Definition deriveAbstraction
           {S:        Type}
           {I:        Type -> Type}
           {A:        Type}
           (abs:      S)
           (abs_step: forall (R: Type), I R -> R -> S -> S)
           (int:      Interp I)
           (p:        Program I A)
  : S :=
  snd (abstractRun abs abs_step int p).

(** * Equality Proofs

    We prove the equality between the results of [runProgram] and
    related and [abstractRun] and related. These proofs are necessary
    to link the properties we could confirm using [abstractRun] and a
    “concrete [Program] execution using [runProgram].

 *)

Lemma abstract_run_run_program_same
      {S: Type}
      {I: Type -> Type}
      {A: Type}
  : forall (p:        Program I A)
           (abs:      S)
           (abs_step: forall (R: Type), I R -> R -> S -> S)
           (int:      Interp I),
    fst (abstractRun abs abs_step int p) = runProgram int p.
Proof.
  induction p; intros abs abs_step int; cbn.
  + reflexivity.
  + apply injective_projections; reflexivity.
  + rewrite H; rewrite IHp; reflexivity.
Qed.

Lemma abstract_eval_eval_program_same
      {S: Type}
      {I: Type -> Type}
      {A: Type}
  : forall (p:        Program I A)
           (abs:      S)
           (abs_step: forall (R: Type), I R -> R -> S -> S)
           (int:      Interp I),
    abstractEval abs abs_step int p = evalProgram int p.
Proof.
  intros p abs abs_step int.
  unfold abstractEval, evalProgram.
  rewrite abstract_run_run_program_same.
  reflexivity.
Qed.

Lemma abstract_exec_exec_program_same
      {S: Type}
      {I: Type -> Type}
      {A: Type}
  : forall (p:        Program I A)
           (abs:      S)
           (abs_step: forall (R: Type), I R -> R -> S -> S)
           (int:      Interp I),
    abstractExec abs abs_step int p = execProgram int p.
Proof.
  intros p abs abs_step int.
  unfold abstractExec, execProgram.
  rewrite abstract_run_run_program_same.
  reflexivity.
Qed.
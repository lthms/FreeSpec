Require Import FreeSpec.Program.
Require Import FreeSpec.Interp.

(** In this library, we provide the functions to

 *)

Fixpoint abstractRun
         {S: Type}
         {I: Type -> Type}
         {A: Type}
         (abs: S)
         (abs_step: forall (R:Type), I R -> S -> S)
         (int: Interp I)
         (p: Program I A)
  : (A * (Interp I) * S) :=
  match p with
  | ret a => (a, int, abs)
  | instr i => (evalInstruction int i,
                execInstruction int i,
                abs_step _ i abs)
  | bind p' f => abstractRun (snd (abstractRun abs abs_step int p'))
                             abs_step
                             (snd (fst (abstractRun abs abs_step int p')))
                             (f (fst (fst (abstractRun abs abs_step int p' ))))
  end.

(** Similary to [FreeSpec.Program.runProgram]

 *)

Definition abstractExec
           {S: Type}
           {I: Type -> Type}
           {A: Type}
           (abs: S)
           (abs_step: forall (R:Type), I R -> S -> S)
           (int: Interp I)
           (p: Program I A)
  : Interp I :=
  snd (fst (abstractRun abs abs_step int p)).

Definition abstractEval
           {S: Type}
           {I: Type -> Type}
           {A: Type}
           (abs: S)
           (abs_step: forall (R:Type), I R -> S -> S)
           (int: Interp I)
           (p: Program I A)
  : A :=
  fst (fst (abstractRun abs abs_step int p)).

Definition deriveAbstraction
           {S: Type}
           {I: Type -> Type}
           {A: Type}
           (abs: S)
           (abs_step: forall (R: Type), I R -> S -> S)
           (int: Interp I)
           (p: Program I A)
  : S :=
  snd (abstractRun abs abs_step int p).

Lemma abstract_run_run_program_same
      {S: Type}
      {I: Type -> Type}
      {A: Type}
  : forall (p: Program I A)
           (abs: S)
           (abs_step: forall (R: Type), I R -> S -> S)
           (int: Interp I),
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
  : forall (p: Program I A)
           (abs: S)
           (abs_step: forall (R: Type), I R -> S -> S)
           (int: Interp I),
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
  : forall (p: Program I A)
           (abs: S)
           (abs_step: forall (R: Type), I R -> S -> S)
           (int: Interp I),
    abstractExec abs abs_step int p = execProgram int p.
Proof.
  intros p abs abs_step int.
  unfold abstractExec, execProgram.
  rewrite abstract_run_run_program_same.
  reflexivity.
Qed.
Require Import FreeSpec.Program.
Require Import FreeSpec.Semantics.

(** In this library, we provide an alternative to [runProgram] we can
    use to derive a so-called abstract state through the executed
    effects of the underlying [Interface]. Using this feature, we can
    verify some properties of a given [Program] _without modifying
    it_.

 *)

(** * Abstract Run

 *)

Fixpoint abstractRun
         {W:         Type}
         {I:         Type -> Type}
         {A:         Type}
         (w:         W)
         (abs_step:  forall (R:Type), I R -> R -> W -> W)
         (sig:       Semantics I)
         (p:         Program I A)
  : (A * (Semantics I) * W) :=
  match p with
  | Pure a
    => (a, sig, w)
  | Request e
    => (evalEffect sig e,
        execEffect sig e,
        abs_step _ e (evalEffect sig e) w)
  | Bind q f
    => abstractRun (snd (abstractRun w abs_step sig q))
                   abs_step
                   (snd (fst (abstractRun w abs_step sig q)))
                   (f (fst (fst (abstractRun w abs_step sig q))))
  end.

(** Similary to [FreeSpec.Program.runProgram], we define several
    helpers functions to select one element among the three that are
    returned by [abstractRun].

 *)

Definition abstractExec
           {W:         Type}
           {I:         Type -> Type}
           {A:         Type}
           (w:         W)
           (abs_step:  forall (R:Type), I R -> R -> W -> W)
           (sig:       Semantics I)
           (p:         Program I A)
  : Semantics I :=
  snd (fst (abstractRun w abs_step sig p)).

Definition abstractEval
           {W:         Type}
           {I:         Type -> Type}
           {A:         Type}
           (w:         W)
           (abs_step:  forall (R:Type), I R -> R -> W -> W)
           (sig:       Semantics I)
           (p:         Program I A)
  : A :=
  fst (fst (abstractRun w abs_step sig p)).

Definition deriveAbstraction
           {W:        Type}
           {I:        Type -> Type}
           {A:        Type}
           (w:        W)
           (abs_step: forall (R: Type), I R -> R -> W -> W)
           (sig:      Semantics I)
           (p:        Program I A)
  : W :=
  snd (abstractRun w abs_step sig p).

(** * Equality Proofs

    We prove the equality between the results of [runProgram] and
    related and [abstractRun] and related. These proofs are necessary
    to link the properties we could confirm using [abstractRun] and a
    “concrete [Program] execution using [runProgram].

 *)

Lemma abstract_run_run_program_same
      {W: Type}
      {I: Type -> Type}
      {A: Type}
  : forall (p:        Program I A)
           (w:        W)
           (abs_step: forall (R: Type), I R -> R -> W -> W)
           (sig:      Semantics I),
    fst (abstractRun w abs_step sig p) = runProgram sig p.
Proof.
  induction p; intros w abs_step sig; cbn.
  + reflexivity.
  + apply injective_projections; reflexivity.
  + rewrite H; rewrite IHp; reflexivity.
Qed.

Lemma abstract_eval_eval_program_same
      {W: Type}
      {I: Type -> Type}
      {A: Type}
  : forall (p:        Program I A)
           (w:        W)
           (abs_step: forall (R: Type), I R -> R -> W -> W)
           (sig:      Semantics I),
    abstractEval w abs_step sig p = evalProgram sig p.
Proof.
  intros p w abs_step sig.
  unfold abstractEval, evalProgram.
  rewrite abstract_run_run_program_same.
  reflexivity.
Qed.

Lemma abstract_exec_exec_program_same
      {W: Type}
      {I: Type -> Type}
      {A: Type}
  : forall (p:        Program I A)
           (w:        W)
           (abs_step: forall (R: Type), I R -> R -> W -> W)
           (sig:      Semantics I),
    abstractExec w abs_step sig p = execProgram sig p.
Proof.
  intros p w abs_step sig.
  unfold abstractExec, execProgram.
  rewrite abstract_run_run_program_same.
  reflexivity.
Qed.
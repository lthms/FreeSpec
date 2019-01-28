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
  | Request e f
    => abstractRun (abs_step _ e (evalEffect sig e) w)
                   abs_step
                   (execEffect sig e)
                   (f (evalEffect sig e))
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
  + rewrite H.
    reflexivity.
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
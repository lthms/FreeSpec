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

Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Logic.Classical.

Require Import Prelude.Equality.

Require Import FreeSpec.Program.
Require Import FreeSpec.Semantics.

(** In this library, we provide an alternative to [runProgram] we can
    use to derive a so-called abstract state through the executed
    effects of the underlying [Interface]. Using this feature, we can
    verify some properties of a given [Program] _without modifying
    it_. *)

(** * Witness State and Instrumented Execution *)

Section def.
Variables (W: Type)
          (I: Interface)
          (abs_step:  forall (R:Type), I R -> R -> W -> W).

Fixpoint runInstrumentedProgram
         {A:         Type}
         (w:         W)
         (sig:       Sem.t I)
         (p:         Program I A)
  : Sem.result I (A * W) :=
  match p with
  | Pure a
    => Sem.mkRes (a, w) sig
  | Request e f
    => runInstrumentedProgram
         (abs_step _ e (evalEffect sig e) w)
         (execEffect sig e)
         (f (evalEffect sig e))
  end.

Lemma runInstrumentedProgram_equation_2
      {A B: Type}
      (w: W)
      (sig: Sem.t I)
      (e: I A)
      (f: A -> Program I B)
  : runInstrumentedProgram w sig (Request e f)
    = runInstrumentedProgram
        (abs_step _ e (evalEffect sig e) w)
        (execEffect sig e)
        (f (evalEffect sig e)).
Proof.
  reflexivity.
Qed.

(** Similary to [FreeSpec.Program.runProgram], we define several
    helpers functions to select one element among the three that are
    returned by [abstractRun].
 *)
Definition execInstrumentedProgram
           {A:         Type}
           (w:         W)
           (sig:       Sem.t I)
           (p:         Program I A)
  : Sem.t I :=
  Sem.next (runInstrumentedProgram w sig p).

Lemma execInstrumentedProgram_equation_2
      {A B: Type}
      (w: W)
      (sig: Sem.t I)
      (e: I A)
      (f: A -> Program I B)
  : execInstrumentedProgram w sig (Request e f)
    = execInstrumentedProgram
        (abs_step _ e (evalEffect sig e) w)
        (execEffect sig e)
        (f (evalEffect sig e)).
Proof.
  reflexivity.
Qed.

Lemma exec_instrumented_exec_same
      {A:         Type}
      (w:         W)
      (sig:       Sem.t I)
      (p:         Program I A)
  : execInstrumentedProgram w sig p = execProgram sig p.
Proof.
  revert w sig.
  induction p.
  + reflexivity.
  + intros w sig.
    rewrite execInstrumentedProgram_equation_2.
    now rewrite H.
Qed.

Definition evalInstrumentedProgram
           {A:         Type}
           (w:         W)
           (sig:       Sem.t I)
           (p:         Program I A)
  : A :=
  fst (Sem.res (runInstrumentedProgram w sig p)).

Lemma evalInstrumentedProgram_equation_2
      {A B: Type}
      (w: W)
      (sig: Sem.t I)
      (e: I A)
      (f: A -> Program I B)
  : evalInstrumentedProgram w sig (Request e f)
    = evalInstrumentedProgram
        (abs_step _ e (evalEffect sig e) w)
        (execEffect sig e)
        (f (evalEffect sig e)).
Proof.
  reflexivity.
Qed.

Lemma eval_instrumented_eval_same
      {A:         Type}
      (w:         W)
      (sig:       Sem.t I)
      (p:         Program I A)
  : evalInstrumentedProgram w sig p = evalProgram sig p.
Proof.
  revert w sig.
  induction p.
  + reflexivity.
  + intros w sig.
    rewrite evalInstrumentedProgram_equation_2.
    now rewrite H.
Qed.

Definition witnessInstrumentedProgram
           {A:        Type}
           (w:        W)
           (sig:      Sem.t I)
           (p:        Program I A)
  : W :=
  snd (Sem.res (runInstrumentedProgram w sig p)).

Lemma witnessInstrumentedProgram_equation_2
      {A B:      Type}
      (w:        W)
      (sig:      Sem.t I)
      (e:        I A)
      (f:        A -> Program I B)
  : witnessInstrumentedProgram w sig (Request e f)
    = witnessInstrumentedProgram
        (abs_step _ e (evalEffect sig e) w)
        (execEffect sig e)
        (f (evalEffect sig e)).
Proof.
  reflexivity.
Qed.

Add Parametric Morphism
    (A: Type) `{Equality A}
  : (witnessInstrumentedProgram)
    with signature eq ==> (@equal (Sem.t I) _) ==> (@equal (Program I A) _) ==> eq
      as derive_abstraction_morphism.
Proof.
  intros w sig sig' Heq_sig p q Heq_p.
  cbn in Heq_p; subst.
  revert w sig sig' Heq_sig.
  induction q.
  + reflexivity.
  + intros w sig sig' [Heq_1 Heq_2].
    repeat rewrite witnessInstrumentedProgram_equation_2.
    rewrite Heq_1.
    apply H0.
    apply Heq_2.
Qed.
End def.

Arguments runInstrumentedProgram [W I] (abs_step) [A] (w sig p).
Arguments evalInstrumentedProgram [W I] (abs_step) [A] (w sig p).
Arguments execInstrumentedProgram [W I] (abs_step) [A] (w sig p).
Arguments witnessInstrumentedProgram [W I] (abs_step) [A] (w sig p).
Arguments exec_instrumented_exec_same [W I] (abs_step) [A] (w sig p).
Arguments eval_instrumented_eval_same [W I] (abs_step) [A] (w sig p).

(** * Abstract Specification

    An Abstract Specification allows for defining an expected
    behaviour for an [Interface] operational [Semantics]. This
    behaviour is expressed with two complementary predicates:

    - The [precondition] an [Interface] user has to enforce
    - The [postcondition] a [Semantics] has to enforce in return

    These predicates are tied to an abstract state. This abstract
    state is modified by the [abstract_step] function through the
    execution (see [abstractRun] for more information about that). *)
Record Specification
       (W:  Type)
       (I:  Type -> Type)
  :=
    { abstract_step (A:  Type)
                    (e:  I A)
                    (x:  A)
      : W -> W
    ; precondition (A:  Type)
      : I A -> W -> Prop
    ; postcondition (A:  Type)
      : I A -> A -> W -> Prop
    }.

Arguments abstract_step [W I] (_) [A] (e x w).
Arguments precondition [W I] (_) [A] (e w).
Arguments postcondition [W I] (_) [A] (e x w).

Definition no_pre
           {I:  Interface}
           {W:  Type}
           (A:  Type)
           (e:  I A)
           (w:  W)
  : Prop :=
  True.

Definition specification_derive
           {W:    Type}
           {I:    Interface}
           {A:    Type}
           (p:    Program I A)
           (sig:  Sem.t I)
           (c:    Specification W I)
           (w:    W)
  : W :=
  witnessInstrumentedProgram (abstract_step c) w sig p.

Fact specification_derives_pure_eq
     {W:    Type}
     {I:    Interface}
     {A:    Type}
     (x:    A)
     (sig:  Sem.t I)
     (c:    Specification W I)
     (w:    W)
  : specification_derive (Pure x) sig c w = w.
Proof.
  reflexivity.
Qed.

Fact specification_derives_request_eq
     (W:    Type)
     (I:    Interface)
     (A B:  Type)
     (e:    I A)
     (f:    A -> Program I B)
     (sig:  Sem.t I)
     (c:    Specification W I)
     (w:    W)
  : specification_derive (Request e f) sig c w
    = specification_derive (f (evalEffect sig e))
                           (execEffect sig e)
                           c
                           (abstract_step c e (evalEffect sig e) w).
Proof.
  reflexivity.
Qed.

(** ** Specification Compliance

    A [Semantics] complies with a given abstract [Specification] [c]
    (i.e. it is a [compliante semantics]) if, for every effect which
    satisfies the [precondition], it computes a result which satisfies
    the [postcondition].

    The abstract Specification is parameterized by an abstract state
    and, by definition, if a [Semantics] complies with a
    [Specification] [c] in accordance with a given abstract state and
    executes an effect which satisfies the precondition, then the
    resulting operational Semantics complies with [c] in accordance
    with the new abstract state computed with the [abstract_step]
    function. *)

CoInductive compliant_semantics
            {W:    Type}
            {I:    Interface}
            (c:    Specification W I)
            (w:    W)
            (sig:  Sem.t I)
  : Prop :=
| enforced (Hprom: forall {A:  Type}
                          (e:  I A),
               precondition c e w
               -> postcondition c e (evalEffect sig e) w)
           (Henf:  forall {A:  Type}
                          (e:  I A),
               precondition c e w
               -> compliant_semantics c
                                      (abstract_step c e (evalEffect sig e) w)
                                      (execEffect sig e))
  : compliant_semantics c w sig.

Notation "sig '|=' c '[' w ']'" :=
  (compliant_semantics c w sig) (at level 60).

Corollary compliant_enforces_postcondition
          (W:     Type)
          (I:     Interface)
          (A:     Type)
          (e:     I A)
          (sig:   Sem.t I)
          (c:     Specification W I)
          (w:     W)
          (Henf:  sig |= c[w])
          (Hreq:  precondition c e w)
  : postcondition c e (evalEffect sig e) w.
Proof.
  destruct Henf.
  now apply Hprom.
Qed.

(** ** Compliant Stateful Semantics *)

Definition specification_preserves_inv
           {W:     Type}
           {I:     Interface}
           {S:     Type}
           (c:     Specification W I)
           (inv:   W -> S -> Prop)
           (step:  @PS I S)
  := forall (A:  Type)
            (e:  I A)
            (w:  W)
            (s:  S),
    inv w s
    -> precondition c e w
    -> inv (abstract_step c e (fst (step A s e)) w) (snd (step A s e)).

Definition specification_enforces_postcondition
           {W:     Type}
           {I:     Interface}
           {S:     Type}
           (c:     Specification W I)
           (inv:   W -> S -> Prop)
           (step:  @PS I S)
  := forall (A:  Type)
            (e:  I A)
            (s:  S)
            (w:  W),
    inv w s
    -> precondition c e w
    -> postcondition c e (fst (step A s e)) w.

Fact _stateful_specification_enforcement
     {W:     Type}
     {I:     Interface}
     {S:     Type}
     (c:     Specification W I)
     (inv:   W -> S -> Prop)
     (step:  @PS I S)
  : forall (w:      W)
           (Hpres:  specification_preserves_inv c inv step)
           (Henf:   specification_enforces_postcondition c inv step)
           (s:      S),
    inv w s
    -> mkSemantics step s |= c[w].
Proof.
  cofix _stateful_specification_enforcement.
  intros w Hpres Henf s Hinv .
  constructor.
  + intros A e Hreq.
    unfold specification_enforces_postcondition in Henf.
    cbn in *.
    apply (Henf A e s w Hinv Hreq).
  + intros A e Hreq.
    apply _stateful_specification_enforcement.
    ++ apply  Hpres.
    ++ apply  Henf.
    ++ cbn in *.
       now eapply Hpres.
Qed.

Lemma stateful_specification_enforcement
      {I:     Interface}
      {W:     Type}
      {S:     Type}
      (c:     Specification W I)
      (w:     W)
      (inv:   W -> S -> Prop)
      (step:  @PS I S)
      (Hpres: specification_preserves_inv c inv step)
      (Henf:  specification_enforces_postcondition c inv step)
  : forall (s: S),
    inv w s
    -> mkSemantics step s |= c[w].
Proof.
  intros s Hinv.
  apply (_stateful_specification_enforcement c inv step w Hpres Henf s Hinv).
Qed.

(** * Correct Program

    In a nutshell, a given [p: Program I A] is said correct with
    respect to a given abstract [Specification] [c] if, given a
    semantics for [I] which complies with [c] in accordance with [w:
    W], [p] only uses effects which satisfy the precondition. *)

(** ** Definition *)

Inductive correct_program
          {W:  Type}
          {I:  Interface}
          (c:  Specification W I)
          (w:  W)
  : forall {A:  Type}, Program I A -> Prop :=
| compliant_pure {A:  Type}
                 (x:  A)
  : correct_program c w (Pure x)
| compliant_request {A B:   Type}
                    (e:     I A)
                    (f:     A -> Program I B)
                    (Hreq:  precondition c e w)
                    (Hnext:  forall (sig: Sem.t I)
                                    (Henf: sig |= c[w]),
                        correct_program c
                                        (abstract_step c e (evalEffect sig e) w)
                                        (f (evalEffect sig e)))
  : correct_program c w (Request e f).

Notation "p '|>' c '[' w ']'" :=
  (correct_program c w p)
    (at level 59, no associativity).

Lemma correct_program_compliant_semantics_compliant_semantics
      {W:  Type}
      {I:  Interface}
      {A:  Type}
      (c:  Specification W I)
      (w:  W)
      (sig: Sem.t I)
      (p: Program I A)
  : sig |= c[w]
    -> p |> c[w]
    -> execProgram sig p |= c[specification_derive p sig c w].
Proof.
  intros Hsig Hp.
  revert sig Hsig.
  induction Hp.
  + auto.
  + intros sig Hsig.
    apply (H sig Hsig).
    destruct Hsig.
    now apply Henf.
Qed.

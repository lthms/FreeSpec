(* FreeSpec
 * Copyright (C) 2018 ANSSI
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

Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import FreeSpec.Semantics.

Require Import Prelude.Equality.
Require Import Prelude.Control.
Require Import Prelude.Control.Classes.

Local Open Scope prelude_scope.

(** * The [Program] Monad

    In this section, we introduce the [Program] Monad. Its definition
    is inspired by the Haskell #<a
    href="https://hackage.haskell.org/package/operational">#operational#</a>#
    package.  Thanks to the [Program] Monad, it becomes easy to
    specify complex programs with effects which belong to a given
    interface.

    To realize a given program, the [runProgram] function is
    provided. This functions takes an operational [Semantics] in
    addition to a [Program] and returns the result of the computation
    along with a new operational semantics. Two helpers functions
    ([evalProgram] and [execProgram]) are provided.

 *)

(** ** Definition

    Given [I] a set of effects (that is, of kind [Interface])
    and [A] the type of the result of a given program, the type of
    this computation specification is [Program I A].

    Under the hood, a [Program] is an AST to wrap and chain several
    call to an underlying interface. More precisely, a [Program] can
    be:

    - [Pure a], a pure value
    - [Request i], a call to the underlying interface through the
      instruction [i]
    - [Bind p f], a first computation whose result determines the
      following computation to execute

 *)

Inductive Program
          (I:  Interface)
          (A:  Type) :=
| Pure (a:  A)
  : Program I A
| Request {B:  Type}
          (e:  I B)
          (f:  B -> Program I A)
  : Program I A.

Arguments Pure [I A] (a).
Arguments Request [I A B] (e f).

(** ** Realisation

    To actually realise a program with effects [Program I A], one
    needs a corresponding operational semantics [Semantics I] for the
    interface described by [I].

 *)

Fixpoint runProgram
         {I:    Interface}
         {A:    Type}
         (sig:  Semantics I)
         (p:    Program I A)
  : (A * Semantics I) :=
  match p with
  | Pure a
    => (a, sig)
  | Request e f
    => runProgram (snd (handle sig e)) (f (fst (handle sig e)))
  end.

Definition singleton
           {I:  Interface}
           {A:  Type}
           (e:  I A)
  : Program I A :=
  Request e (@Pure I A).

Definition evalProgram
           {I:    Interface}
           {A:    Type}
           (sig:  Semantics I)
           (p:    Program I A)
  : A :=
  fst (runProgram sig p).

Definition execProgram
           {I:   Interface}
           {A:   Type}
           (sig: Semantics I)
           (p:   Program I A)
  : Semantics I :=
  snd (runProgram sig p).

(** ** [Program]s Weak Equality

    Two [Program] are equal when they always gives both the exact same
    result and two equivalent semantics (according to [semantics_eq]),
    no matter the input semantics.

 *)

Instance program_Eq
         (I:  Interface)
         (A:  Type)
  : Equality (Program I A) :=
  { equal := eq
  }.

(** Also, we can easily show the [program_eq] property is strong
    enough to be used to replace two equivalent programs in several
    cases, by defining the related morphisms.

 *)

Add Parametric Morphism
    (I: Interface)
    (A: Type)
  : (runProgram)
    with signature (@semantics_eq I) ==> (@equal (Program I A) _) ==> (@run_semantics_eq I A)
  as run_program_morphism_2.
Proof.
  intros sig1 sig2 Heq_sig p q Heq_p.
  induction Heq_p.
  revert sig1 sig2 Heq_sig.
  induction p; intros sig1 sig2 Heq_sig.
  + constructor; [ reflexivity |].
    apply Heq_sig.
  + cbn.
    assert (Hx: fst (handle sig1 e) = fst (handle sig2 e)) by apply Heq_sig.
    rewrite Hx.
    apply H.
    apply Heq_sig.
Qed.

Add Parametric Morphism
    (I:  Interface)
    (A:  Type)
  : (execProgram)
    with signature (@equal (Semantics I) _) ==> (@equal (Program I A) _) ==> (@semantics_eq I)
  as exec_program_morphism.
Proof.
  intros sig sig' Heqs p q Heqp.
  unfold execProgram.
  rewrite Heqs.
  rewrite Heqp.
  reflexivity.
Qed.

Add Parametric Morphism
    (I:  Interface)
    (A:  Type)
  : (evalProgram)
    with signature (@equal (Semantics I) _) ==> (@equal (Program I A) _) ==> eq
  as eval_program_morphism.
Proof.
  intros sig sig' Heqs p q Heqp.
  unfold evalProgram.
  rewrite Heqs.
  rewrite Heqp.
  reflexivity.
Qed.

Lemma program_eq_sig_eq
      {I:    Type -> Type}
      {A:    Type} `{Equality A}
      (p q:  Program I A)
  : p == q
    -> forall (sig sig':  Semantics I),
      sig == sig'
      -> evalProgram sig p == evalProgram sig' q.
Proof.
  intros Heq sig1 sig2 Heq_sig.
  rewrite Heq_sig.
  rewrite Heq.
  reflexivity.
Qed.

Lemma program_eq_res_eq
      {I:    Type -> Type}
      {A:    Type}
      (p q:  Program I A)
  : p == q
    -> forall (sig sig':  Semantics I),
      sig == sig'
      -> evalProgram sig p = evalProgram sig' q.
Proof.
  intros Heq sig1 sig2 Heq_sig.
  rewrite Heq_sig.
  rewrite Heq.
  reflexivity.
Qed.

(** ** Monad Laws

    [Program] _is_ a Monad and therefore obeys the Monad laws.  The
    #<a href="https://wiki.haskell.org/Monad_laws">#Haskell Wiki#</a>#
    explains in depth what are the laws and why they are usefull. In a
    nutshell, the laws are intended to ease the use of a given Monad
    by a programmer by making the monad functionning in general more
    predictible. By conforming to the Monad laws, one knows its monad
    will have more chance to behave the way its users may expect it
    to.

    Fortunately, in our case, proving the Monad laws is straightforward.

 *)

Fixpoint pbind
         {I:    Interface}
         {A B:  Type}
         (p:    Program I A)
         (f:    A -> Program I B)
  : Program I B :=
  match p with
  | Pure x => f x
  | Request e g => Request e (fun x => pbind (g x) f)
  end.

Lemma run_program_bind_assoc
      {I:    Interface}
      {A B:  Type}
      (sig:  Semantics I)
      (p:    Program I A)
      (f:    A -> Program I B)
  : runProgram sig (pbind p f)
    == runProgram (execProgram sig p) (f (evalProgram sig p)).
Proof.
  revert sig; induction p; intro sig.
  + reflexivity.
  + apply H.
Qed.

Lemma eval_program_bind_assoc
      {I:    Interface}
      {A B:  Type}
      (sig:  Semantics I)
      (p:    Program I A)
      (f:    A -> Program I B)
  : evalProgram sig (pbind p f)
    = evalProgram (execProgram sig p) (f (evalProgram sig p)).
Proof.
  unfold evalProgram.
  rewrite run_program_bind_assoc.
  reflexivity.
Qed.

Lemma exec_program_bind_assoc
      {I:    Interface}
      {A B:  Type}
      (sig:  Semantics I)
      (p:    Program I A)
      (f:    A -> Program I B)
  : execProgram sig (pbind p f)
    = execProgram (execProgram sig p) (f (evalProgram sig p)).
Proof.
  revert sig; induction p; intro sig.
  + reflexivity.
  + apply H.
Qed.

Lemma program_eq_append_pure
      {I:  Type -> Type}
      {A:  Type}
      (p:  Program I A)
  : p = pbind p (@Pure I A).
Proof.
  induction p.
  + reflexivity.
  + cbn.
    apply functional_extensionality in H.
    rewrite <- H.
    reflexivity.
Qed.

Lemma program_eq_bind_assoc
      {I:      Type -> Type}
      {A B C:  Type}
      (p:      Program I A)
      (f:      A -> Program I B)
      (g:      B -> Program I C)
  : pbind (pbind p f) g = pbind p (fun x => pbind (f x) g).
Proof.
  induction p; [reflexivity |].
  cbn.
  apply functional_extensionality in H.
  rewrite H.
  reflexivity.
Qed.

Definition program_map
           {I:    Interface}
           {A B:  Type}
           (f:    A -> B)
           (p:    Program I A)
  : Program I B :=
  pbind p (fun x => Pure (f x)).

Instance program_Functor
         (I:  Interface)
  : Functor (Program I) :=
  { map := @program_map I
  }.
Proof.
  + intros A HA x.
    unfold program_map.
    rewrite <- program_eq_append_pure.
    reflexivity.
  + intros A B C HC u v x.
    unfold compose.
    unfold program_map.
    rewrite program_eq_bind_assoc.
    reflexivity.
Defined.

Definition program_apply
           {I:    Interface}
           {A B:  Type}
           (pf:   Program I (A -> B))
           (p:    Program I A)
  : Program I B :=
  pbind pf (fun f => pbind p (fun x => Pure (f x))).

Definition program_pure
           {I:  Interface}
           {A:  Type}
  : A -> Program I A :=
  @Pure I A.

Lemma program_eq_bind
      {I:    Type -> Type}
      {A B:  Type}
      (p:    Program I A)
      (f g:  A -> Program I B)
  : f = g -> pbind p f = pbind p g.
Proof.
  intros R; rewrite R.
  reflexivity.
Qed.

Instance program_Applicative
         (I:  Interface)
  : Applicative (Program I) :=
  { pure := @program_pure I
  ; apply := @program_apply I
  }.
Proof.
  + intros A HA p.
    unfold program_apply, program_pure.
    cbn.
    rewrite <- program_eq_append_pure.
    reflexivity.
  + intros A B C HC u v p.
    unfold program_apply, program_pure.
    cbn.
    repeat rewrite program_eq_bind_assoc.
    cbn.
    apply program_eq_bind.
    apply functional_extensionality.
    intros x.
    repeat rewrite program_eq_bind_assoc.
    apply program_eq_bind.
    apply functional_extensionality.
    intros y.
    cbn.
    repeat rewrite program_eq_bind_assoc.
    apply program_eq_bind.
    apply functional_extensionality.
    intros z.
    reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
Defined.

Instance program_Monad
         (I:  Interface)
  : Monad (Program I) :=
  { bind := @pbind I
  }.
Proof.
  + reflexivity.
  + intros A Ha p.
    cbn.
    rewrite <- program_eq_append_pure.
    reflexivity.
  + intros A B C HC x f g.
    rewrite program_eq_bind_assoc.
    reflexivity.
  + intros A B HB p f g Heq.
    cbn in Heq.
    unfold function_equal in Heq.
    cbn in Heq.
    apply program_eq_bind.
    now apply functional_extensionality.
  + intros A B HB p f.
    cbn.
    reflexivity.
Defined.

(** ** Alternative [Program] Execution

    We provide the function [runProgram'] as a probably more efficient
    way to run a given Program. The difference is actually quite
    simple: [runProgram] makes no use of the [let ... in] feature
    because our tests have shown Coq sometimes have some trouble
    dealing with this construction. As a consequence, some calls are
    made twice or even more.

    Thanks to the [run_program_equiv] lemma, one can use [runProgram]
    for her proofs and extract [runProgram'].

 *)
Fixpoint runProgram'
         {I:    Interface}
         {A:    Type}
         (sig:  Semantics I)
         (p:    Program I A)
  : (A * Semantics I) :=
  match p with
  | Pure a
    => (a, sig)
  | Request e f
    => let o := handle sig e
       in runProgram' (snd o) (f (fst o))
  end.

Lemma run_program_equiv
      {I:   Interface}
      {A:   Type}
      (sig: Semantics I)
      (p:   Program I A)
  : runProgram sig p = runProgram' sig p.
Proof.
  induction p; reflexivity.
Qed.

Fixpoint interface_map
         {I I':  Interface}
         {A:     Type}
         (p:     Program I A)
         (map:   forall {A:  Type}, I A -> I' A)
  : Program I' A :=
  match p with
  | Pure x
    => Pure x
  | Request e f
    => Request (map e) (fun x => interface_map (f x) (fun _ x => map x))
  end.
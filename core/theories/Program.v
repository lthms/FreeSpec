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

(** * The [Program] Monad *)

(** In this section, we introduce the [Program] Monad. Its definition
    was originally inspired by the Haskell #<a
    href="https://hackage.haskell.org/package/operational">#operational#</a>#
    package, and then has been simplified following the example of the
    [itree] (see “From C to Interaction Trees” by the DeepWeb
    project).

    Thanks to the [Program] Monad, it becomes easy to
    specify complex programs with effects which belong to a given
    interface. *)

(*  To realize a given program, the [runProgram] function is
    provided. This functions takes an operational [Sem.t] in
    addition to a [Program] and returns the result of the computation
    along with a new operational semantics. Two helpers functions
    ([evalProgram] and [execProgram]) are provided. *)

(** ** Definition

    Given [I] a set of effects (that is, of kind [Interface])
    and [A] the type of the result of a given program, the type of
    this computation specification is [Program I A].

    Under the hood, an instance of the [Program] monad wraps and
    chains several calls to an underlying interface. More precisely,
    [Program] has two constructors:

    - [Pure a], which describes the (pure) computation of the value
      [a]
    - [Request i f], which describes a call to the underlying
      interface through the instruction [i] and a continuation [f] to
      process this result *)

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

(** ** Working with Arbitrary Interfaces *)

(** In practice, one computation may require more than one
    [Interface]s, which means we need to be able to compose Interfaces
    together. The Library [FreeSpec.Compose] provides several
    abstraction to that end.

    This poses a challenge in terms of [Program] specifications
    reusability. Thanks to the [bind] function, [Program]
    specifications can be composed together, but #<i>#they need to
    share the same [Interface]#</i>#. To overcome this challenge, we
    follow the example of the Haskell #<a
    href="https://hackage.haskell.org/package/extensible-effects">#extensible-effects#</a>#
    package. Thanks to the [Use] typeclass, we can specify which
    interfaces a given [Program] specification uses, yet leave the
    actual interface abstract. *)
Class Use (i ix: Interface)
  := { lift_eff (a:  Type): i a -> ix a
     }.

(** The most obvious instance of [Use] is [Use i i]. *)
Instance Instance_Use (i: Interface): Use i i :=
  { lift_eff := fun _ => id
  }.

Arguments lift_eff [i ix _ a] (e).

(** Using the [Use] typeclass, we can implement a more generic
    replacement of the old definition of the [Request]
    constructor.

    As a reminder, in the first iterations of FreeSpec, [Request] was
    a constructor of type [i a -> Program i a], to model a computation
    that consists in waiting for the result of an operation and
    returning this very result.

    We now introduce [request]. Its purposes is similar, but thanks to
    [Use], this functions can be used more easily in a [Program]
    specification with a different interface type. *)
Definition request
           {i:   Type -> Type}
           {ix:  Type -> Type} `{Use i ix}
           {a:   Type}
           (e:   i a)
  : Program ix a :=
  Request (lift_eff e) (@Pure ix a).

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

(** ** Monad Laws

    [Program] _is_ a Monad and therefore obeys the Monad laws.  The
    #<a href="https://wiki.haskell.org/Monad_laws">#Haskell Wiki#</a>#
    explains in depth what are the laws and why they are usefull. In a
    nutshell, the laws are intended to ease the use of a given Monad
    by a programmer by making the monad functionning in general more
    predictible. By conforming to the Monad laws, one knows its monad
    will have more chance to behave the way its users may expect it
    to.

    Fortunately, in our case, proving the Monad laws is
    straightforward. *)

Fixpoint program_bind
         {I:    Interface}
         {A B:  Type}
         (p:    Program I A)
         (f:    A -> Program I B)
  : Program I B :=
  match p with
  | Pure x => f x
  | Request e g => Request e (fun x => program_bind (g x) f)
  end.

Lemma program_eq_append_pure
      {I:  Type -> Type}
      {A:  Type}
      (p:  Program I A)
  : p = program_bind p (@Pure I A).
Proof.
  induction p.
  + reflexivity.
  + cbn.
    apply functional_extensionality in H.
    now rewrite <- H.
Qed.

Lemma program_eq_bind_assoc
      {I:      Type -> Type}
      {A B C:  Type}
      (p:      Program I A)
      (f:      A -> Program I B)
      (g:      B -> Program I C)
  : program_bind (program_bind p f) g = program_bind p (fun x => program_bind (f x) g).
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
  program_bind p (fun x => Pure (f x)).

#[program]
Instance program_Functor
         (I:  Interface)
  : Functor (Program I) :=
  { map := @program_map I
  }.
Next Obligation. (* program_map id x = id x *)
  unfold program_map.
  rewrite <- program_eq_append_pure.
  reflexivity.
Defined.
Next Obligation. (* program_map (v >>> u) x = (program_map v >>> program_map u) x *)
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
  program_bind pf (fun f => map f p).

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
  : f = g -> program_bind p f = program_bind p g.
Proof.
  intros R; rewrite R.
  reflexivity.
Qed.

#[polymorphic, program]
Instance program_Applicative
         (I:  Interface)
  : Applicative (Program I) :=
  { pure := @program_pure I
  ; apply := @program_apply I
  }.
Next Obligation. (* program_apply (program_pure id) v = v *)
  unfold program_apply, program_pure, program_bind.
  now rewrite functor_identity.
Defined.
Next Obligation. (* program_apply (program_apply (program_apply (program_pure compose) u) v) w
                    = program_apply u (program_apply v w) *)
  unfold program_apply, program_pure.
  cbn.
  unfold program_map.
  repeat rewrite program_eq_bind_assoc.
  apply program_eq_bind.
  apply functional_extensionality.
  intros x.
  cbn.
  unfold program_map.
  repeat rewrite program_eq_bind_assoc.
  apply program_eq_bind.
  apply functional_extensionality.
  intros y.
  cbn.
  repeat rewrite program_eq_bind_assoc.
  apply program_eq_bind.
  apply functional_extensionality.
  intros z.
  cbn.
  unfold compose.
  reflexivity.
Defined.

#[program]
Instance program_Monad
         (I:  Interface)
  : Monad (Program I) :=
  { bind := @program_bind I
  }.
Next Obligation.
  now rewrite <- program_eq_append_pure.
Defined.
Next Obligation.
  now rewrite program_eq_bind_assoc.
Defined.
Next Obligation.
  apply program_eq_bind.
  now apply functional_extensionality.
Defined.

(** * [Program] Interpretation

    To actually realise a program with effects [Program I A], one
    needs a corresponding operational semantics [Sem.t I] for the
    interface described by [I].
 *)

Fixpoint runProgram
         {I:    Interface}
         {A:    Type}
         (sig:  Sem.t I)
         (p:    Program I A)
  : Sem.result I A :=
  match p with
  | Pure a
    => Sem.mkRes a sig
  | Request e f
    => let res := handle sig e in
       runProgram (Sem.next res) (f (Sem.res res))
  end.

Definition evalProgram
           {I:    Interface}
           {A:    Type}
           (sig:  Sem.t I)
           (p:    Program I A)
  : A :=
  Sem.res (runProgram sig p).

Definition execProgram
           {I:   Interface}
           {A:   Type}
           (sig: Sem.t I)
           (p:   Program I A)
  : Sem.t I :=
  Sem.next (runProgram sig p).

(** Also, we can easily show the [program_eq] property is strong
    enough to be used to replace two equivalent programs in several
    cases, by defining the related morphisms.

 *)
Add Parametric Morphism
    (I: Interface)
    (A: Type)
  : (runProgram)
    with signature (@equal (Sem.t I) _) ==> (@equal (Program I A) _) ==> (@equal (Sem.result I A) _)
  as run_program_morphism_2.
Proof.
  intros sig1 sig2 Heq_sig p q Heq_p.
  induction Heq_p.
  revert sig1 sig2 Heq_sig.
  induction p; intros sig1 sig2 Heq_sig.
  + now constructor.
  + cbn.
    assert (Hx: Sem.res (handle sig1 e) = Sem.res (handle sig2 e)) by apply Heq_sig.
    rewrite Hx.
    apply H.
    apply Heq_sig.
Qed.

Add Parametric Morphism
    (I:  Interface)
    (A:  Type)
  : (execProgram)
    with signature (@equal (Sem.t I) _) ==> (@equal (Program I A) _) ==> (@equal (Sem.t I) _)
  as exec_program_morphism.
Proof.
  intros sig sig' Heqs p q Heqp.
  unfold execProgram.
  rewrite Heqs.
  now rewrite Heqp.
Qed.

Add Parametric Morphism
    (I:  Interface)
    (A:  Type)
  : (evalProgram)
    with signature (@equal (Sem.t I) _) ==> (@equal (Program I A) _) ==> eq
  as eval_program_morphism.
Proof.
  intros sig sig' Heqs p q Heqp.
  unfold evalProgram.
  rewrite Heqs.
  now rewrite Heqp.
Qed.

Lemma run_program_bind_assoc
      {I:    Interface}
      {A B:  Type}
      (sig:  Sem.t I)
      (p:    Program I A)
      (f:    A -> Program I B)
  : runProgram sig (program_bind p f)
    == runProgram (execProgram sig p) (f (evalProgram sig p)).
Proof.
  revert sig; induction p; intro sig.
  + reflexivity.
  + apply H.
Qed.

Lemma eval_program_bind_assoc
      {I:    Interface}
      {A B:  Type}
      (sig:  Sem.t I)
      (p:    Program I A)
      (f:    A -> Program I B)
  : evalProgram sig (program_bind p f)
    = evalProgram (execProgram sig p) (f (evalProgram sig p)).
Proof.
  unfold evalProgram.
  rewrite run_program_bind_assoc.
  reflexivity.
Qed.

Lemma exec_program_bind_assoc
      {I:    Interface}
      {A B:  Type}
      (sig:  Sem.t I)
      (p:    Program I A)
      (f:    A -> Program I B)
  : execProgram sig (program_bind p f)
    = execProgram (execProgram sig p) (f (evalProgram sig p)).
Proof.
  revert sig; induction p; intro sig.
  + reflexivity.
  + apply H.
Qed.

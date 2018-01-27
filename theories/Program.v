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

Require Import FreeSpec.Semantics.
Require Import FreeSpec.WEq.
Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Classes.

Local Open Scope free_weq_scope.

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
          (I: Interface)
          (A: Type) :=
| Pure (a:  A)
  : Program I A
| Request (e:  I A)
  : Program I A
| Bind {B:  Type}
       (p:  Program I B)
       (f:  B -> Program I A)
  : Program I A.

Arguments Pure [I A] (a).
Arguments Request [I A] (e).
Arguments Bind [I A B] (p f).

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
  | Request e
    => handle sig e
  | Bind q f
    => runProgram (snd (runProgram sig q)) (f (fst (runProgram sig q)))
  end.

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

CoInductive program_eq
            {I:    Interface}
            {A:    Type}
            (p q:  Program I A)
  : Prop :=
| program_is_eq (Hres: forall (sig: Semantics I),
                    evalProgram sig p = evalProgram sig q)
(*
  TODO: Do we really need the semantics equivalence? maybe the Leibniz
  equality is enough
 *)
                (Hnext: forall (sig: Semantics I),
                    execProgram sig p == execProgram sig q)
  : program_eq p q.

(**
    We can easily prove this property is indeed and equivalence by
    showing it is reflexive, symmetric and transitive.

 *)

Lemma program_eq_refl
      {I:  Interface}
      {A:  Type}
      (p:  Program I A)
  : program_eq p p.
Proof.
  constructor; reflexivity.
Qed.

Lemma program_eq_sym
      {I:     Interface}
      {A:     Type}
      (p p':  Program I A)
  : program_eq p p'
    -> program_eq p' p.
Proof.
  intro H1.
  destruct H1 as [Hres Hnext].
  constructor.
  + intro sig.
    rewrite Hres.
    reflexivity.
  + intro sig.
    rewrite Hnext.
    reflexivity.
Qed.

Lemma program_eq_trans
      {I:         Interface}
      {A:         Type}
      (p p' p'':  Program I A)
  : program_eq p p'
    -> program_eq p' p''
    -> program_eq p p''.
Proof.
  intros [Hres1 Hnext1] [Hres2 Hnext2].
  constructor; intro sig.
  + transitivity (evalProgram sig p').
    ++ apply Hres1.
    ++ apply Hres2.
  + transitivity (execProgram sig p').
    ++ apply Hnext1.
    ++ apply Hnext2.
Qed.

Add Parametric Relation
    (I:  Interface)
    (A:  Type)
  : (Program I A) (program_eq)
    reflexivity  proved by (program_eq_refl)
    symmetry     proved by (program_eq_sym)
    transitivity proved by (program_eq_trans)
      as program_equiv.

Instance program_WEq
         (I:  Interface)
         (A:  Type)
  : WEq (Program I A) :=
  { weq := program_eq
  }.

(** Also, we can easily show the [program_eq] property is strong
    enough to be used to replace two equivalent programs in several
    cases, by defining the related morphisms.

 *)

Lemma run_program_bind_assoc
      {I:    Interface}
      {A B:  Type}
      (sig:  Semantics I)
      (p:    Program I A)
      (f:    A -> Program I B)
  : runProgram sig (Bind p f)
    == runProgram (execProgram sig p) (f (evalProgram sig p)).
Proof.
  reflexivity.
Qed.

Lemma eval_program_bind_assoc
      {I:    Interface}
      {A B:  Type}
      (sig:  Semantics I)
      (p:    Program I A)
      (f:    A -> Program I B)
  : evalProgram sig (Bind p f)
    = evalProgram (execProgram sig p) (f (evalProgram sig p)).
Proof.
  reflexivity.
Qed.

Lemma exec_program_bind_assoc
      {I:    Interface}
      {A B:  Type}
      (sig:  Semantics I)
      (p:    Program I A)
      (f:    A -> Program I B)
  : execProgram sig (Bind p f)
    = execProgram (execProgram sig p) (f (evalProgram sig p)).
Proof.
  reflexivity.
Qed.

Add Parametric Morphism
    (I:  Interface)
    (A:  Type)
  : (runProgram)
    with signature eq ==> (@weq (Program I A) _) ==> (@run_semantics_eq I A)
  as run_program_morphism_1.
Proof.
  intros y p p' Heq.
  constructor.
  destruct Heq.
  + apply Hres.
  + apply Heq.
Qed.

Add Parametric Morphism
    (I: Interface)
    (A: Type)
  : (runProgram)
    with signature (@semantics_eq I) ==> eq ==> (@run_semantics_eq I A)
  as run_program_morphism_2.
Proof.
  intros sig sig' Heq p.
  revert sig sig' Heq.
  induction p; intros sig sig' Heq.
  + cbn.
    constructor; [ reflexivity
                 | exact Heq
                 ].
  + cbn.
    destruct Heq as [Hres Hnext].
    constructor; [ apply Hres
                 | apply Hnext
                 ].
  + repeat rewrite run_program_bind_assoc.
    assert (rw:  evalProgram sig p = evalProgram sig' p). {
      apply IHp.
      exact Heq.
    }
    rewrite rw.
    apply H.
    apply IHp.
    exact Heq.
Qed.

Add Parametric Morphism
    (I:  Interface)
    (A:  Type)
  : (evalProgram)
    with signature (@weq (Semantics I) _) ==> (@program_eq I A) ==> (eq)
  as eval_program_morphism.
Proof.
  intros sig sig' Heqs p q Heqp.
  unfold evalProgram.
  rewrite Heqs.
  rewrite Heqp.
  reflexivity.
Qed.

Add Parametric Morphism
    (I:  Interface)
    (A:  Type)
  : (execProgram)
    with signature (@weq (Semantics I) _) ==> (@program_eq I A) ==> (@semantics_eq I)
  as exec_program_morphism.
Proof.
  intros sig sig' Heqs p q Heqp.
  unfold execProgram.
  rewrite Heqs.
  rewrite Heqp.
  reflexivity.
Qed.

Add Parametric Morphism
    (I:      Interface)
    (A B C:  Type)
  : (@Bind I B A)
    with signature (@weq (Program I A) _)
                     ==> (@eq (A -> Program I B))
                     ==> (@weq (Program I B) _)
      as pbind_morphism.
Proof.
  intros p q Heq f.
  constructor; intros sig.
  + repeat rewrite eval_program_bind_assoc.
    rewrite Heq.
    reflexivity.
  + repeat rewrite exec_program_bind_assoc.
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

Definition program_map
           {I:    Interface}
           {A B:  Type}
           (f:    A -> B)
           (p:    Program I A)
  : Program I B :=
  Bind p (fun x => Pure (f x)).

Instance program_Functor
         (I:  Interface)
  : Functor (Program I) :=
  { map := @program_map I
  }.
Proof.
  + intros A x.
    constructor; reflexivity.
  + intros A B C f g p.
    constructor; reflexivity.
Defined.

Definition program_apply
           {I:    Interface}
           {A B:  Type}
           (pf:   Program I (A -> B))
           (p:    Program I A)
  : Program I B :=
  Bind pf (fun f => Bind p (fun x => Pure (f x))).

Definition program_pure
           {I:  Interface}
           {A:  Type}
  : A -> Program I A :=
  @Pure I A.

Instance program_Applicative
         (I:  Interface)
  : Applicative (Program I) :=
  { pure := @program_pure I
  ; apply := @program_apply I
  }.
Proof.
  + intros A p.
    constructor; reflexivity.
  + intros A B C u v p.
    constructor; reflexivity.
  + intros A B v x.
    constructor; reflexivity.
  + intros A B u y.
    constructor; reflexivity.
  + intros A B HB g p.
    constructor; reflexivity.
Defined.

Definition program_bind
           {I:    Interface}
           {A B:  Type}
  : Program I A -> (A -> Program I B) -> Program I B :=
  @Bind I B A.

Instance program_Monad
         (I:  Interface)
  : Monad (Program I) :=
  { bind := @program_bind I
  }.
Proof.
  + constructor; reflexivity.
  + constructor; reflexivity.
  + constructor; reflexivity.
  + intros A B HB p f f' Heq.
    unfold program_bind.
    constructor.
    ++ intros sig.
       assert (R1: forall (sig: Semantics I)
                          (f: A -> Program I B),
                  evalProgram sig (Bind p f)
                  = evalProgram (execProgram sig p) (f (evalProgram sig p)))
         by reflexivity.
       rewrite R1.
       rewrite R1.
       assert (R2: f (evalProgram sig p) == f' (evalProgram sig p))
         by apply Heq.
       rewrite R2.
       reflexivity.
    ++ intros sig.
       assert (R1: forall (sig: Semantics I)
                          (f: A -> Program I B),
                  execProgram sig (Bind p f)
                  == execProgram (execProgram sig p) (f (evalProgram sig p)))
         by reflexivity.
       rewrite R1.
       rewrite R1.
       assert (R2: f (evalProgram sig p) == f' (evalProgram sig p))
         by apply Heq.
       rewrite R2.
       reflexivity.
  + intros A B HB g p.
    constructor; reflexivity.
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
  | Request e
    => handle sig e
  | Bind q f
    => let o := runProgram' sig q
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
         (map:   forall (A:  Type), I A -> I' A)
  : Program I' A :=
  match p with
  | Pure x
    => Pure x
  | Request e
    => Request (map A e)
  | Bind q f
    => Bind (interface_map q map) (fun x => interface_map (f x) map)
  end.

(** * Notations

 *)

Notation  "[ i ]" := (Request i) (at level 50) : free_prog_scope.
Notation "'[ i ]" := (lift (Request i)) (at level 50) : free_prog_scope.
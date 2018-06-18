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

Inductive program_eq
          {I:  Type -> Type}
          {A:  Type}
  : Program I A -> Program I A -> Prop :=
| program_eq_refl (p:  Program I A)
  : program_eq p p
| program_eq_sym (p q:  Program I A)
                  (H:    program_eq p q)
  : program_eq q p
| program_eq_trans (p q r:  Program I A)
                    (Hpq:   program_eq p q)
                    (Hqr:   program_eq q r)
  : program_eq p r
| program_eq_append_pure (p:  Program I A)
  : program_eq p (Bind p (@Pure I A))
| program_eq_bind_ret {B:  Type}
                       (x:  B)
                       (f:  B -> Program I A)
  : program_eq (Bind (Pure x) f) (f x)
| program_eq_bind_assoc {B C:  Type}
                         (p:   Program I B)
                         (f:   B -> Program I C)
                         (g:   C -> Program I A)
  : program_eq (Bind (Bind p f) g) (Bind p (fun x => Bind (f x) g))
| program_eq_bind {B:    Type}
                   (p q:  Program I B)
                   (f g:  B -> Program I A)
                   (Hpq:  @program_eq I B p q)
                   (Hfg:  forall (x:  B), program_eq (f x) (g x))
  : program_eq (Bind p f) (Bind q g).

Add Parametric Relation
    (I:  Interface)
    (A:  Type)
  : (Program I A) (program_eq)
    reflexivity  proved by program_eq_refl
    symmetry     proved by program_eq_sym
    transitivity proved by program_eq_trans
      as program_equiv.

Instance program_Eq
         (I:  Interface)
         (A:  Type)
  : Equality (Program I A) :=
  { equal := program_eq
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
    (I: Interface)
    (A: Type)
  : (runProgram)
    with signature (@semantics_eq I) ==> eq ==> (@run_semantics_eq I A)
  as run_program_morphism_2.
Proof.
  intros sig1 sig2 Heq_sig p.
  revert sig1 sig2 Heq_sig.
  induction p; intros sig1 sig2 Heq_sig.
  + constructor; [ reflexivity |].
    apply Heq_sig.
  + constructor; apply Heq_sig.
  + repeat rewrite run_program_bind_assoc.
    assert (rw:  evalProgram sig1 p = evalProgram sig2 p). {
      apply IHp.
      exact Heq_sig.
    }
    rewrite rw.
    apply H.
    apply IHp.
    exact Heq_sig.
Qed.

Add Parametric Morphism
    (I:  Interface)
    (A:  Type)
  : (runProgram)
    with signature eq ==> (@equal (Program I A) _) ==> (@run_semantics_eq I A)
  as run_program_morphism_1.
Proof.
  intros sig p q Heq.
  revert sig.
  induction Heq; intros sig.
  + reflexivity.
  + symmetry.
    apply (IHHeq sig).
  + etransitivity; [ apply (IHHeq1 sig)
                   | apply (IHHeq2 sig)
                   ].
  + constructor; reflexivity.
  + constructor; reflexivity.
  + constructor; reflexivity.
  + repeat rewrite run_program_bind_assoc.
    assert (Hstep: run_semantics_eq (runProgram sig p) (runProgram sig q))
      by apply IHHeq.
    assert (rw:  execProgram sig p == execProgram sig q) by apply Hstep.
    assert (rw': evalProgram sig p = evalProgram sig q) by apply Hstep.
    rewrite rw.
    rewrite rw'.
    apply H.
Qed.

Add Parametric Morphism
    (I:  Interface)
    (A:  Type)
  : (evalProgram)
    with signature (@equal (Semantics I) _) ==> (@program_eq I A) ==> (eq)
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
    with signature (@equal (Semantics I) _) ==> (@program_eq I A) ==> (@semantics_eq I)
  as exec_program_morphism.
Proof.
  intros sig sig' Heqs p q Heqp.
  unfold execProgram.
  rewrite Heqs.
  rewrite Heqp.
  reflexivity.
Qed.

Add Parametric Morphism
    (I:    Interface)
    (A B:  Type)
  : (@Bind I B A)
    with signature (@equal (Program I A) _)
                     ==> (@equal (A -> Program I B) _)
                     ==> (@equal (Program I B) _)
      as pbind_morphism.
Proof.
  intros p q Heq f g Heq_f.
  constructor.
  apply program_eq_bind.
  + symmetry.
    exact Heq.
  + intros x.
    symmetry.
    apply Heq_f.
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
  + intros A HA x.
    unfold program_map.
    rewrite <- program_eq_append_pure.
    reflexivity.
  + intros A B C HC u v x.
    unfold compose.
    unfold program_map.
    rewrite program_eq_bind_assoc.
    apply program_eq_bind; [ reflexivity |].
    intros y.
    rewrite program_eq_bind_ret.
    reflexivity.
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
  + intros A HA p.
    unfold program_apply, program_pure.
    rewrite program_eq_bind_ret.
    rewrite <- program_eq_append_pure.
    reflexivity.
  + intros A B C HC u v p.
    unfold program_apply, program_pure.
    rewrite program_eq_bind_ret.
    repeat rewrite program_eq_bind_assoc.
    apply program_eq_bind; [ reflexivity |].
    intros x.
    rewrite program_eq_bind_ret.
    repeat rewrite program_eq_bind_assoc.
    apply program_eq_bind; [ reflexivity |].
    intros y.
    unfold compose.
    rewrite program_eq_bind_ret.
    repeat rewrite program_eq_bind_assoc.
    apply program_eq_bind; [ reflexivity |].
    intros z.
    rewrite program_eq_bind_ret.
    reflexivity.
  + intros A B HB v x.
    unfold program_apply, program_pure.
    repeat rewrite program_eq_bind_ret.
    reflexivity.
  + intros A B HA u y.
    unfold program_apply, program_pure.
    repeat rewrite program_eq_bind_ret.
    apply program_eq_bind; [ reflexivity |].
    intros x.
    repeat rewrite program_eq_bind_ret.
    reflexivity.
  + intros A B HA g x.
    cbn.
    unfold program_map, program_apply, program_pure.
    rewrite program_eq_bind_ret.
    apply program_eq_bind; [ reflexivity |].
    reflexivity.
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
  + intros A B HB x f.
    apply program_eq_bind_ret.
  + intros A HA x.
    unfold program_bind.
    rewrite <- program_eq_append_pure.
    reflexivity.
  + intros A B C HC f g h.
    unfold program_bind.
    apply program_eq_bind_assoc.
  + intros A B HB x f g Heq.
    rewrite Heq.
    reflexivity.
  + intros A B HA x f.
    cbn.
    unfold program_map, program_bind.
    apply program_eq_bind; [ reflexivity |].
    intros y.
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

Inductive View
          (I:  Type -> Type)
          (A:  Type)
  : Type :=
| Result (x:  A)
  : View I A
| Seq {B:    Type}
      (eff:  I B)
      (f:    B -> Program I A)
  : View I A.

Arguments Result {I A} (x).
Arguments Seq {I A B} (eff f).

Require Import FunInd.

Function view
         {I:  Type -> Type}
         {A:  Type}
         (p:  Program I A)
  : View I A :=
  match p with
  | Pure x
    => Result x
  | Request eff
    => Seq eff (@Pure I A)
  | Bind p f
    => match view p with
       | Result x
         => view (f x)
       | Seq eff h
         => Seq eff (fun x => Bind (h x) f)
       end
  end.

Theorem program_eq'_eval_eq
        {I:    Type -> Type}
        {A:    Type}
        (p q:  Program I A)
  : p == q -> forall (sig:  Semantics I),
      runProgram sig p = runProgram sig q.
Proof.
  intros Heq.
  induction Heq; intros sig.
  + reflexivity.
  + symmetry.
    apply IHHeq.
  + transitivity (runProgram sig q).
    ++ apply IHHeq1.
    ++ apply IHHeq2.
  + cbn.
    destruct (runProgram sig p).
    reflexivity.
  + reflexivity.
  + reflexivity.
  + cbn.
    rewrite IHHeq.
    rewrite H.
    reflexivity.
Qed.

Function simplify
         {I:  Type -> Type}
         {A:  Type}
         (p:  Program I A)
  : Program I A :=
  match view p with
  | Result x
    => Pure x
  | Seq eff f
    => Bind (Request eff) f
  end.

Theorem simplify_eq
        {I:  Type -> Type}
        {A:  Type}
        (p:  Program I A)
  : p == (simplify p).
Proof.
  induction p.
  + apply program_eq_refl.
  + cbn.
    apply program_eq_append_pure.
  + assert ((simplify (Bind p f))
            == (Bind (simplify p) (fun x => simplify (f x)))). {
      functional induction (simplify p).
      + unfold simplify.
        cbn.
        rewrite e.
        fold (simplify (f x)).
        eapply program_eq_trans.
        apply program_eq_sym.
        apply H.
        apply program_eq_sym.
        eapply program_eq_trans.
        eapply program_eq_bind_ret.
        fold (simplify (f x)).
        apply program_eq_sym.
        apply H.
      + unfold simplify.
        cbn.
        rewrite e.
        eapply program_eq_trans.
        apply program_eq_sym.
        apply program_eq_bind_assoc.
        apply program_eq_bind.
        apply program_eq_refl.
        intros x.
        fold (simplify (f x)).
        apply H.
    }
    apply program_eq_trans with (q:=(Bind (simplify p) (fun x : B => simplify (f x)))).
    ++ apply program_eq_bind.
       apply IHp.
       apply H.
    ++ apply program_eq_sym.
       apply H0.
Qed.

(* FIXME: not enough *)
Theorem program_request_seq_ind
        {I:       Type -> Type}
        {A:       Type}
        (P:       Program I A -> Prop)
        (Hmorph:  forall (p q:  Program I A),
            p == q -> (P p <-> P q))
        (Hres:   forall (x:  A), P (Pure x))
        (Hseq:   forall {B:    Type}
                        (eff:  I B)
                        (f:    B -> Program I A),
            P (Bind (Request eff) f))
  : forall (p:  Program I A),
    P p.
Proof.
  intros p.
  assert (Hsimp:  p == (simplify p)) by apply simplify_eq.
  apply (Hmorph (simplify p) p (program_eq_sym _ _ Hsimp)).
  functional induction (simplify p).
  + apply Hres.
  + apply Hseq.
Qed.
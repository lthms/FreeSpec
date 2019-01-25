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

Require Import Coq.Classes.Equivalence.
Require Import Coq.Setoids.Setoid.
Require Export FreeSpec.Interface.
Require Import Prelude.Equality.

Local Open Scope prelude_scope.

(** * [Semantics]

    In a nutshell, an operational Semantics is function which takes an
    effect of a given [Interface] and returns both a result and a new
    Semantics. This choice of model has been made to abstract away how
    a Semantics is implemented, in particular regarding its potential
    state. A stateless Semantics will simply returns itself when a
    stateful one will carry a state, yet both can be use rigourously
    the same way.

    Therefore, a Semantics is defined as a coinductive type
    [Semantics] and is provided along with [handle], a function to
    actually compute the result of the effect. Because a Semantics
    returns a tuple, a type which is not always great to work with, we
    provide [evalEffect] and [execEffect] as shortcuts. Their naming
    follows the same logic as the Haskell state monad functions.

 *)

CoInductive Semantics
            (I: Interface)
  : Type :=
| handler (f: forall {A: Type}, I A -> A * Semantics I)
  : Semantics I.

Arguments handler [I] (f).

Definition handle
           {I:    Interface}
           {A:    Type}
           (sig:  Semantics I)
           (e:    I A)
  : (A * Semantics I) :=
  match sig with handler f => f A e end.

Definition evalEffect
           {I:    Interface}
           {A:    Type}
           (sig:  Semantics I)
           (e:    I A)
  : A :=
  fst (handle sig e).

Definition execEffect
           {I:    Interface}
           {A:    Type}
           (sig:  Semantics I)
           (e:    I A)
    : Semantics I :=
    snd (handle sig e).

CoFixpoint coerce_semantics
           {I I':  Interface}
           (f:     forall (A:  Type), I A -> I' A)
           (sig:   Semantics I')
  : Semantics I :=
  handler (fun (A:  Type)
               (e:  I A)
           => (evalEffect sig (f _ e), coerce_semantics f (execEffect sig (f _ e)))).

(** ** Semantics Equivalence

    Two Semantics are said to be equivalent when they always return
    the exact same result and when their resulting Semantics are
    equivalent themselves.

 *)

CoInductive semantics_eq
            {I:     Interface}
            (sig1:  Semantics I)
            (sig2:  Semantics I)
  : Prop :=
| semantics_is_eq (Hres: forall {A:  Type}
                                (e:  I A),
                      evalEffect sig1 e = evalEffect sig2 e)
                  (Hnext: forall {A:  Type}
                                 (e:  I A),
                      semantics_eq (execEffect sig1 e) (execEffect sig2 e))
  : semantics_eq sig1 sig2.

(** We prove [semantics_eq] is indeed an equivalence.

 *)

Lemma semantics_eq_refl
      {I:  Interface}
  : forall (sig: Semantics I),
    semantics_eq sig sig.
Proof.
  cofix semantics_eq_refl.
  intros int.
  constructor.
  + reflexivity.
  + intros A i.
    apply semantics_eq_refl.
Qed.

Lemma semantics_eq_sym
      {I:  Interface}
  : forall (sig sig': Semantics I),
    semantics_eq sig sig'
    -> semantics_eq sig' sig.
Proof.
  cofix semantics_eq_sym.
  intros sig sig' H1.
  destruct H1.
  constructor.
  + intros A e.
    symmetry.
    exact (Hres A e).
  + intros A e.
    apply (semantics_eq_sym (execEffect sig e) (execEffect sig' e) (Hnext A e)).
Qed.

Lemma semantics_eq_trans
      {I:  Interface}
  : forall (sig sig' sig'':  Semantics I),
    semantics_eq sig sig'
    -> semantics_eq sig' sig''
    -> semantics_eq sig sig''.
Proof.
  cofix semantics_eq_trans.
  intros sig sig' sig'' H1 H2.
  destruct H1 as [Hres1 Hnext1].
  destruct H2 as [Hres2 Hnext2].
  constructor.
  + intros A e.
    transitivity (evalEffect sig' e).
    exact (Hres1 A e).
    exact (Hres2 A e).
  + intros A e.
    apply (semantics_eq_trans (execEffect sig   e)
                              (execEffect sig'  e)
                              (execEffect sig'' e)
                              (Hnext1 A e)
                              (Hnext2 A e)).
Qed.

Add Parametric Relation
    (I:  Interface)
  : (Semantics I) (semantics_eq)
  reflexivity  proved by (semantics_eq_refl)
  symmetry     proved by (semantics_eq_sym)
  transitivity proved by (semantics_eq_trans)
    as semantics_rel.

Instance semantics_Equality
         (I:  Interface)
  : Equality (Semantics I) :=
  {| equal := @semantics_eq I |}.

(** ** Semantics Result Weak Equality

    To help Coq when it comes to generalized rewriting, we define an
    equivalence relation for the result we get with [handle], along
    with several morphisms.
 *)

Definition run_semantics_eq
           {I:     Interface}
           {A:     Type}
           (r r':  (A * Semantics I))
  : Prop :=
  fst r = fst r' /\ snd r == snd r'.

Lemma run_semantics_eq_refl
      {I:  Interface}
      {A:  Type}
      (x:  (A * Semantics I))
  : run_semantics_eq x x.
Proof.
  constructor; reflexivity.
Qed.

Lemma run_semantics_eq_sym
           {I:    Interface}
           {A:    Type}
           (x y:  (A * Semantics I))
  : run_semantics_eq x y
    -> run_semantics_eq y x.
Proof.
  intros [H H']; symmetry in H; symmetry in H'.
  constructor; [exact H|exact H'].
Qed.

Lemma run_semantics_eq_trans
           {I:     Interface}
           {A:     Type}
           (x y z: (A * Semantics I))
  : run_semantics_eq x y
    -> run_semantics_eq y z
    -> run_semantics_eq x z.
Proof.
  intros [H H'] [G G'].
  constructor.
  + rewrite H; exact G.
  + rewrite H'; exact G'.
Qed.

Add Parametric Relation
    (I:  Interface)
    (A:  Type)
  : (A * Semantics I) (@run_semantics_eq I A)
    reflexivity  proved by (run_semantics_eq_refl)
    symmetry     proved by (run_semantics_eq_sym)
    transitivity proved by (run_semantics_eq_trans)
      as run_semantics_equiv.

Instance run_semantics_Eq
         {I: Interface}
         {A: Type}
  : Equality (A * Semantics I) :=
  { equal := run_semantics_eq
  }.

(** We then provide the several morphisms to be able to rewrite terms
    using the [run_semantics_eq] equivalence relation.

 *)

Add Parametric Morphism
    (I:  Interface)
    (A:  Type)
  : (@fst A (Semantics I))
    with signature (run_semantics_eq) ==> (@eq A)
  as fst_program_morphism.
Proof.
  intros o o' [H _H].
  exact H.
Qed.

Add Parametric Morphism
    (I:  Interface)
    (A:  Type)
  : (@snd A (Semantics I))
    with signature (run_semantics_eq) ==> (semantics_eq)
  as snd_program_morphism.
Proof.
  intros o o' [_H H].
  exact H.
Qed.

Add Parametric Morphism
    (I: Interface)
    (A: Type)
  : (handle)
    with signature (@semantics_eq I) ==> (@eq (I A)) ==> (run_semantics_eq)
      as semantics_handle_morphism.
Proof.
  intros sig sig' Heq e.
  constructor.
  + destruct Heq.
    apply (Hres A e).
  + destruct Heq.
    assert (Hin:  semantics_eq (execEffect sig e) (execEffect sig' e))
      by (apply Hnext).
    apply Hnext.
Qed.

Add Parametric Morphism
    (I:  Interface)
    (A:  Type)
  : (evalEffect)
    with signature (@semantics_eq I) ==> (@eq (I A)) ==> (eq)
      as eval_effect_morphism.
Proof.
  intros sig sig' Heq e.
  unfold evalEffect.
  rewrite Heq.
  reflexivity.
Qed.

Add Parametric Morphism
    (I: Interface)
    (A: Type)
  : (execEffect)
    with signature (@semantics_eq I) ==> (@eq (I A)) ==> (@semantics_eq I)
      as exec_effect_morphism.
Proof.
  intros sig sig' Heq i.
  unfold execEffect.
  rewrite Heq.
  reflexivity.
Qed.

(* begin hide *)

(* A list of goal to check the rewrite tactic actually works *)

Goal (forall (I:         Interface)
             (sig sig':  Semantics I)
             (A:         Type)
             (eqA:       Equality A)
             (e:         I A),
         sig == sig'
         -> evalEffect sig e == evalEffect sig' e).
Proof.
  intros I sig sig' A eqA e Heq.
  rewrite Heq.
  reflexivity.
Qed.

Goal (forall (I:         Interface)
             (sig sig':  Semantics I)
             (A:         Type)
             (eqA:       Equality A)
             (e:         I A),
         sig == sig'
         -> execEffect sig e == execEffect sig' e).
Proof.
  intros I sig sig' A eqA e Heq.
  rewrite Heq.
  reflexivity.
Qed.
(* end hide *)

(** * Stateful Semantics

    The function [mkSemantics] is here to ease the definition of new
    so-called stateful semantics. More precisely, it turns a function
    which, given an internal state and an effect to handle, returns a
    new state and the instruction result. [mkSemantics] wraps this
    function to make it an operational [Semantics].

 *)

Definition PS
           {I:      Interface}
           (State:  Type)
  := forall (A: Type), State -> I A -> (A * State).

CoFixpoint mkSemantics
           {I:      Interface}
           {State:  Type}
           (ps:     PS State)
           (s:      State)
  : Semantics I :=
  handler (
      fun (A:  Type)
          (e:  I A) =>
        (fst (ps A s e), mkSemantics ps (snd (ps A s e)))).

(** * Semantics for Labeled Effects

    We can enrich an Semantics to handle labelled Effects. It will
    just ignore the labels, which is basically what we want. However,
    when we will define abstract specification for our Interfaces, we
    can use the label to give a more precise definition based on usage
    context.

    *)

Local Open Scope free_scope.

Definition enrich_semantics
           {I:    Interface}
           (L:    Type)
           (int:  Semantics I)
  : Semantics (I <?> L) :=
  mkSemantics (fun (A:    Type)
                   (sig:  Semantics I)
                   (e:    (I <?> L) A)
               => match e with
                  | e <:> _
                    => handle sig e
                  end)
              int.
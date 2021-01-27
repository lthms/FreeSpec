(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From ExtLib Require Import StateMonad.
From FreeSpec.Core Require Import Contract HoareFacts SemanticsFacts InstrumentFacts.
From FreeSpec Require Export Component.

(** We use an alternative definition of [derive_semantics], which has
    the virtue of being easier to reason with. More precisely, it
    behaves better with evaluation tactics such as [cbn] (according to
    our experience, [derive_semantics] requires explicit [destruct]
    call to deal with the [let ... in ...]  construction).

    This is a detail of implementation of our proof, henceforth the
    definition is local and should not be used anywhere else. *)

#[local]
CoFixpoint derive_semantics' {i j} (c : component i j) (sem : semantics j)
  : semantics i :=
  mk_semantics (fun a p =>
                  (evalState (to_state $ c a p) sem,
                   derive_semantics' c (execState (to_state $ c a p) sem))).

(** We prove these two definitions ([derive_semantics] and
    [derive_semantics']) are equivalent wrt. [semantics_eq]. *)

#[local]
Remark derive_semantics_equ `(c : component i j) (sem : semantics j)
  : (derive_semantics c sem === derive_semantics' c sem)%semantics.

Proof.
  revert sem.
  cofix aux; intros sem.
  constructor; intros a e;
    cbn;
    unfold derive_semantics;
    unfold eval_effect;
    unfold exec_effect;
    unfold run_effect;
    unfold evalState;
    unfold execState;
    destruct runState.
  + reflexivity.
  + apply aux.
Qed.

(** ** Component Correctness *)

(** We consider a component [c : component i j s], meaning [c] exposes an
    interface [i], uses an interface [j], and carries an internal state of type
    [s].

<<
                            c : component i j s
                        i +---------------------+      j
                        | |                     |      |
                +------>| |       st : s        |----->|
                        | |                     |      |
                          +---------------------+
>>

    We say [c] is correct wrt. [ci] (a contract for [i]) and [cj] (a contract
    for [i]) iff given primitives which satisfies the caller obligation of [ci],
    [c] will

    - use respectful impure computations wrt. [cj]
    - compute results which satisfy [ci] callee obligations, assuming it can
      rely on a semantics of [j] which complies with [cj]

    The two witness states [ωi : Ωi] (for [speci]) and [ωj : Ωj] (for [specj]),
    and [st : s] the internal state of [c] remained implicit in the previous
    sentence.  In practice, we associate them together by means of a dedicated
    predicate [pred].  It is expected that [pred] is an invariant throughout
    [c]'s life, meaning that as long as [c] computes result for legitimate
    effects (wrt.  [speci] effects, the updated values of [ωi], [ωj] and [st]
    continue to satisfy [pred]. *)

Definition correct_component `{MayProvide jx j}
   `(c : component i jx) `(ci : contract i Ωi) `(cj : contract j Ωj)
    (pred : Ωi -> Ωj -> Prop)
  : Prop :=
   forall (ωi : Ωi) (ωj : Ωj) (init : pred ωi ωj)
         `(e : i α) (o_caller : caller_obligation ci ωi e),
    pre (to_hoare cj $ c α e) ωj /\
    forall (x : α) (ωj' : Ωj) (run : post (to_hoare cj $ c α e) ωj x ωj'),
      callee_obligation ci ωi e x /\ pred (witness_update ci ωi e x) ωj'.

(** Once we have proven [c] is correct wrt. to [speci] and [specj] with [pred]
    acting as an invariant throughout [c] life, we show we can derive a
    semantics from [c] with an initial state [st] which complies to [speci] in
    accordance to [ωi] if we use a semantics of [j] which complies to [specj] in
    accordance to [ωj], where [pred ωi st ωj] is satisfied. *)

Lemma correct_component_derives_compliant_semantics `{MayProvide jx j}
   `(c : component i jx) `(ci : contract i Ωi) `(cj : contract j Ωj)
    (pred : Ωi -> Ωj -> Prop)
    (correct : correct_component c ci cj pred)
    (ωi : Ωi) (ωj : Ωj) (inv : pred ωi ωj)
    (sem : semantics jx) (comp : compliant_semantics cj ωj sem)
  : compliant_semantics ci ωi (derive_semantics c sem).

Proof.
  rewrite derive_semantics_equ.
  revert ωi ωj inv sem comp.
  cofix correct_component_derives_compliant_semantics.
  intros ωi ωj inv sem comp.
  unfold correct_component in correct.
  specialize (correct ωi ωj inv).
  constructor; intros a e req; specialize (correct a e req);
    destruct correct as [trust run].
  + eapply run.
    cbn.
    ++ rewrite instrument_to_state_eval_morphism with (c0 := cj) (ω := ωj).
       now apply instrument_satisfies_hoare.
  + eapply correct_component_derives_compliant_semantics.
    ++ apply run.
       cbn.
       erewrite instrument_to_state_eval_morphism.
       apply instrument_satisfies_hoare.
       +++ exact comp.
       +++ exact trust.
    ++ erewrite instrument_to_state_exec_morphism.
       apply instrument_preserves_compliance.
       +++ exact comp.
       +++ apply trust.
Qed.

(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From ExtLib Require Import StateMonad.
From FreeSpec.Core Require Import Contract HoareFacts SemanticsFacts.
From FreeSpec.Core Require Export Instrument.

Lemma instrument_to_state_eval_morphism `{MayProvide ix i}
   `(c : contract i Ω) `(p : impure ix a) (ω : Ω)
  : forall (sem : semantics ix),
    evalState (to_state p) sem
    = fst (evalState (runStateT (to_instrument c p) ω) sem).

Proof.
  unfold evalState.
  revert ω.
  induction p.
  + reflexivity.
  + intros ω sem.
    cbn -[gen_witness_update].
    destruct run_effect; cbn.
    now rewrite H0 with (ω := gen_witness_update c ω e β0).
Qed.

Lemma instrument_to_state_exec_morphism `{MayProvide ix i}
   `(c : contract i Ω) `(p : impure ix a) (ω : Ω)
  : forall (sem : semantics ix),
    execState (to_state p) sem
    = execState (runStateT (to_instrument c p) ω) sem.

Proof.
  unfold execState.
  revert ω.
  induction p.
  + reflexivity.
  + intros ω sem.
    cbn -[gen_witness_update].
    destruct run_effect; cbn.
    now rewrite H0 with (ω := gen_witness_update c ω e β0).
Qed.

Lemma instrument_satisfies_hoare `{MayProvide ix i}
   `(c : contract i Ω) `(p : impure ix a)
   `(comp : compliant_semantics c ω sem)
  : pre (to_hoare c p) ω
    -> post
         (to_hoare c p)
         ω
         (fst $ evalState (runStateT (to_instrument c p) ω) sem)
         (snd $ evalState (runStateT (to_instrument c p) ω) sem).

Proof.
  revert comp. revert ω. revert sem.
  induction p; intros sem ω comp.
  + cbn.
    intros _.
    split; reflexivity.
  + intros pre.
    cbn -[interface_to_hoare] in pre.
    destruct pre as [He Hf].
    cbn in He.
    inversion comp; subst.
    pose proof He as He'.
    apply o_callee in He.
    cbn.
    exists (eval_effect sem e).
    exists (gen_witness_update c ω e (eval_effect sem e)).
    split; [split |].
    ++ apply He.
    ++ reflexivity.
    ++ unfold evalState. cbn.
       repeat rewrite run_effect_equation.
       apply H0.
       +++ apply next.
           apply He'.
       +++ apply Hf.
           cbn.
           now split.
Qed.

Lemma instrument_preserves_compliance `{MayProvide ix i}
   `(c : contract i Ω) `(p : impure ix a)
   `(comp : compliant_semantics c ω sem)
  : pre (to_hoare c p) ω
    -> compliant_semantics
         c
         (snd $ evalState (runStateT (to_instrument c p) ω) sem)
         (execState (runStateT (to_instrument c p) ω) sem).

Proof.
  revert comp. revert ω. revert sem.
  induction p; intros sem ω comp pre.
  + auto.
  + cbn in pre.
    destruct pre as [He Hn].
    specialize Hn with (eval_effect sem e)
                       (gen_witness_update (H := H) c ω e (eval_effect sem e)).
    inversion comp; subst.
    assert (Hn' : pre (to_hoare c (f (eval_effect sem e))) (gen_witness_update c ω e (eval_effect sem e))). {
      apply Hn.
      split; [| reflexivity].
      now apply o_callee.
    }
    eapply H0 in Hn'; [| now apply next ].
    replace (snd (evalState (runStateT (to_instrument c (request_then e f)) ω) sem))
      with (snd
             (evalState
                (runStateT (to_instrument c (f (eval_effect sem e)))
                   (gen_witness_update c ω e (eval_effect sem e))) (exec_effect sem e))).
    replace (execState (runStateT (to_instrument c (request_then e f)) ω) sem)
      with (execState
             (runStateT (to_instrument c (f (eval_effect sem e)))
                (gen_witness_update c ω e (eval_effect sem e))) (exec_effect sem e)).
    ++ apply Hn'.
    ++ cbn.
       unfold execState at 2. cbn.
       now rewrite run_effect_equation.
    ++ cbn.
       unfold evalState at 2. cbn.
       now rewrite run_effect_equation.
Qed.

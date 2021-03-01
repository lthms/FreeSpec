(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From ExtLib Require Import StateMonad.

From FreeSpec.Core Require Import ImpureFacts Contract.
From FreeSpec.Core Require Export Semantics.

(** * Semantics Compliance *)

(** Given a semantics [sem], and a witness [ω] if [sem] computes results which
    satisfies [c] callee obligations for effects which satisfy [c] caller
    obligations and if the resulting semantics produces after interpreting [e]
    complies to [c] in accordance to [ω'], where [ω'] is the new witness state
    after [e] interpretation then [sem] complies to [c] in accordance to [ω] *)

CoInductive compliant_semantics `{MayProvide ix i} `(c : contract i Ω)
  : Ω -> semantics ix -> Prop :=
| compliant_semantics_rec
    (sem : semantics ix) (ω : Ω)
    (o_callee : forall {α} (e : ix α),
        gen_caller_obligation c ω e -> gen_callee_obligation c ω e (eval_effect sem e))
    (next : forall {α} (e : ix α),
        gen_caller_obligation c ω e
        -> compliant_semantics c (gen_witness_update c ω e (eval_effect sem e)) (exec_effect sem e))
  : compliant_semantics c ω sem.

(** Proving that semantics obtained from the [store] function are compliant with
    [store_specs] is relatively simple. *)

Lemma store_complies_to_store_specs {s} (st : s)
  : compliant_semantics (store_specs s) st (store st).

Proof.
  revert st; cofix compliant_semantics_rec; intros st.
  constructor.
  + intros a [| st'] _.
    ++ now constructor.
    ++ now constructor.
  + intros a e req.
    cbn.
    replace (exec_effect (store st) e)
      with (store (store_update s st a e (eval_effect (store st) e)))
      by now destruct e as [| st'].
    apply compliant_semantics_rec.
Qed.

#[global] Hint Resolve store_complies_to_store_specs : freespec.

Lemma compliant_semantics_caller_obligation_callee_obligation `{MayProvide ix i}
   `(c : contract i Ω) (ω : Ω)
   `(e : ix α) (o_caller : gen_caller_obligation c ω e)
    (sem : semantics ix) (comp : compliant_semantics c ω sem)
  : gen_callee_obligation c ω e (eval_effect sem e).

Proof.
  inversion comp; ssubst.
  now apply o_callee.
Qed.

#[global] Hint Resolve compliant_semantics_caller_obligation_callee_obligation : freespec.

Lemma compliant_semantics_caller_obligation_compliant `{MayProvide ix i} {Ω α} (c : contract i Ω) (ω : Ω)
  (e : ix α) (o_caller : gen_caller_obligation c ω e)
  (sem : semantics ix) (comp : compliant_semantics c ω sem)
  : compliant_semantics c (gen_witness_update c ω e (eval_effect sem e)) (exec_effect sem e).

Proof.
  inversion comp; ssubst.
  now apply next.
Qed.

#[global] Hint Resolve compliant_semantics_caller_obligation_compliant : freespec.

Lemma no_contract_compliant_semantics `{MayProvide ix i} (sem : semantics ix) (u : unit)
  : compliant_semantics (no_contract i) u sem.

Proof.
  revert sem.
  cofix no_contract_compliant_semantics; intros sem.
  constructor.
  + intros α e req.
    unfold gen_caller_obligation, gen_callee_obligation.
    destruct proj_p; constructor.
  + intros α e req.
    unfold gen_witness_update.
    destruct (proj_p e); [ apply no_contract_compliant_semantics | auto with freespec ].
Qed.

#[global] Hint Resolve no_contract_compliant_semantics : freespec.

(** * Equivalences *)

(** ** Semantics *)

(** We say two semantics are equivalent when they produce equivalent outputs
    given the same primitive. *)

CoInductive semantics_eq {i} : semantics i -> semantics i -> Prop :=
| semantics_eq_rec
    (sem sem' : semantics i)
    (res_eq : forall {a} (e : i a), eval_effect sem e = eval_effect sem' e)
    (next_eq : forall {a} (e : i a),
        semantics_eq (exec_effect sem e) (exec_effect sem' e))
  : semantics_eq sem sem'.

Infix "===" := semantics_eq : semantics_scope.

(** We prove [semantics_eq] is indeed an equivalence. *)

#[program]
Instance semantics_Equivalence (i : interface) : Equivalence (@semantics_eq i).

Next Obligation.
  cofix semantics_eq_refl.
  intros sem.
  constructor; intros α e.
  + reflexivity.
  + apply semantics_eq_refl.
Qed.

Next Obligation.
  cofix semantics_eq_sym.
  intros sem sem' equiv.
  destruct equiv as [sem sem' step].
  constructor; intros α e.
  + now symmetry.
  + now apply semantics_eq_sym.
Qed.

Next Obligation.
  cofix semantics_eq_trans.
  intros sem sem' sem'' equiv equiv'.
  destruct equiv as [sem sem' equ].
  destruct equiv' as [sem' sem'' equ'].
  constructor; intros α e;
    specialize equ with α e;
    specialize equ' with α e;
    inversion equ; ssubst;
      inversion equ'; ssubst.
  + now transitivity (eval_effect sem' e).
  + eapply semantics_eq_trans; [ apply next_eq | apply next_eq0 ].
Qed.

(** ** Interpretation Results *)

Definition run_effect_eq `(x : α * semantics i) (y : α * semantics i) : Prop :=
  fst x = fst y /\ (snd x === snd y)%semantics.

#[program]
Instance run_effect_Equivalence a i
  : @Equivalence (a * semantics i) run_effect_eq.

Next Obligation.
  intros [x next]; now split.
Qed.

Next Obligation.
  intros [x next] [y next'] [H1 H2]; now split.
Qed.

Next Obligation.
  intros [x next] [y next'] [z next_] [H1 H2] [H3 H4].
  split; etransitivity; eauto.
Qed.

(** ** Proper Instances *)

#[program]
Instance fst_Proper i α
  : Proper (run_effect_eq ==> eq) (@fst α (semantics i)).

Next Obligation.
  add_morphism_tactic.
  intros [x next] [y next'] [equ1 equ2].
  apply equ1.
Qed.

#[program]
Instance snd_Proper i α
  : Proper (run_effect_eq ==> semantics_eq) (@snd α (semantics i)).

Next Obligation.
  add_morphism_tactic.
  intros [x next] [y next'] [equ1 equ2].
  apply equ2.
Qed.

#[program]
Instance prod_Proper i α
  : Proper (eq ==> semantics_eq ==> run_effect_eq) (@pair α (semantics i)).

Next Obligation.
  add_morphism_tactic.
  intros x sem sem' equ.
  split.
  + reflexivity.
  + apply equ.
Qed.

Instance run_effect_Proper i α
  : Proper (semantics_eq ==> eq ==> run_effect_eq) (@run_effect i α).

Proof.
  add_morphism_tactic.
  intros sem sem' equ e.
  rewrite run_effect_equation.
  inversion equ; subst.
  split.
  + apply res_eq.
  + apply next_eq.
Qed.

#[program]
Instance eval_effect_Proper i α
  : Proper (semantics_eq ==> eq ==> eq) (@eval_effect i α).

Next Obligation.
  add_morphism_tactic.
  intros o o' equ e.
  unfold eval_effect.
  now rewrite equ.
Qed.

#[program]
Instance exec_effect_Proper i α
  : Proper (semantics_eq ==> eq ==> semantics_eq) (@exec_effect i α).

Next Obligation.
  add_morphism_tactic.
  intros o o' equ e.
  unfold exec_effect.
  now rewrite equ.
Qed.

#[local]
Remark eval_semprod_in_left_eq `(semi : semantics i) `(semj : semantics j) `(e : i α)
  : eval_effect (semi * semj) (in_left e) = eval_effect semi e.

Proof.
  unfold eval_effect; cbn.
  destruct semi as [semi].
  cbn.
  now destruct (semi α e).
Qed.

#[local]
Remark eval_semprod_in_right_eq `(semi : semantics i) `(semj : semantics j) `(e : j α)
  : eval_effect (semi * semj) (in_right e) = eval_effect semj e.

Proof.
  unfold eval_effect; cbn.
  destruct semj as [semj].
  cbn.
  now destruct (semj α e).
Qed.

#[local]
Remark exec_semprod_in_left_eq `(semi : semantics i) `(semj : semantics j) `(e : i α)
  : exec_effect (semi * semj) (in_left e) = (semprod (exec_effect semi e) semj).

Proof.
  unfold exec_effect; cbn.
  destruct semi as [semi].
  cbn.
  now destruct (semi _ e).
Qed.

#[local]
Remark exec_semprod_in_right_eq `(semi : semantics i) `(semj : semantics j) `(e : j α)
  : exec_effect (semi * semj) (in_right e) = (semprod semi (exec_effect semj e)).

Proof.
  unfold exec_effect; cbn.
  destruct semj as [semj].
  cbn.
  now destruct (semj _ e).
Qed.

#[program]
Instance semprod_Proper i j
  : Proper (semantics_eq ==> semantics_eq ==> semantics_eq) (@semprod i j).

Next Obligation.
  add_morphism_tactic.
  cofix semprod_Proper.
  intros semi semi' equi semj semj' equj.
  constructor; intros α e; destruct e.
  + repeat rewrite eval_semprod_in_left_eq.
    now inversion equi.
  + repeat rewrite eval_semprod_in_right_eq.
    now inversion equj.
  + repeat rewrite exec_semprod_in_left_eq.
    apply semprod_Proper; auto.
    inversion equi.
    apply next_eq.
  + repeat rewrite exec_semprod_in_right_eq.
    apply semprod_Proper; auto.
    inversion equj.
    apply next_eq.
Qed.

#[program]
Instance compliant_semantics_Proper `{MayProvide ix i} `(c : contract i Ω)
  : Proper (eq ==> semantics_eq ==> Basics.impl) (compliant_semantics c).

Next Obligation.
  add_morphism_tactic.
  unfold Basics.impl.
  cofix proper.
  intros ω sem sem' equ comp.
  inversion equ; subst.
  inversion comp; subst.
  constructor; intros a e pre.
  + rewrite <- res_eq.
    now apply o_callee.
  + specialize next_eq with a e.
    eapply proper.
    exact next_eq.
    rewrite <- res_eq.
    now apply next.
Qed.

(** * General Lemmas *)

(** We provide several lemmas and the necessary [Proper] instances to use these
    functions in conjunction with [semantics_equiv] and [impure_equiv]. *)

Lemma run_impure_equation {i a} (sem : semantics i) (p : impure i a)
  : run_impure sem p = (eval_impure sem p, exec_impure sem p).

Proof.
  unfold eval_impure, exec_impure.
  destruct run_impure; reflexivity.
Qed.

Lemma run_impure_request_then_assoc {i a b}
    (sem : semantics i) (e : i a) (f : a -> impure i b)
  : run_impure sem (request_then e f)
    = run_impure (exec_effect sem e) (f (eval_effect sem e)).

Proof.
  cbn; now rewrite run_effect_equation.
Qed.

Lemma eval_impure_request_then_assoc {i a b}
    (sem : semantics i) (e : i a) (f : a -> impure i b)
  : eval_impure sem (request_then e f)
    = eval_impure (exec_effect sem e) (f (eval_effect sem e)).

Proof.
  unfold eval_impure.
  now rewrite run_impure_request_then_assoc.
Qed.

Lemma exec_impure_request_then_assoc {i a b}
    (sem : semantics i) (e : i a) (f : a -> impure i b)
  : exec_impure sem (request_then e f)
    = exec_impure (exec_effect sem e) (f (eval_effect sem e)).

Proof.
  unfold exec_impure.
  now rewrite run_impure_request_then_assoc.
Qed.

Lemma run_impure_bind_assoc {i a b}
    (sem : semantics i) (p : impure i a) (f : a -> impure i b)
  : run_impure sem (p >>= f)
    = run_impure (exec_impure sem p) (f (eval_impure sem p)).

Proof.
  revert sem f.
  induction p; intros sem g.
  + reflexivity.
  + rewrite bind_request_then_assoc.
    rewrite run_impure_request_then_assoc.
    rewrite H.
    rewrite exec_impure_request_then_assoc.
    rewrite eval_impure_request_then_assoc.
    reflexivity.
Qed.

Lemma eval_impure_bind_assoc {i a b}
    (sem : semantics i) (p : impure i a) (f : a -> impure i b)
  : eval_impure sem (p >>= f)
    = eval_impure (exec_impure sem p) (f (eval_impure sem p)).

Proof.
  unfold eval_impure.
  now rewrite run_impure_bind_assoc.
Qed.

Lemma exec_impure_bind_assoc {i a b}
    (sem : semantics i) (p : impure i a) (f : a -> impure i b)
  : exec_impure sem (p >>= f)
    = exec_impure (exec_impure sem p) (f (eval_impure sem p)).

Proof.
  unfold exec_impure.
  now rewrite run_impure_bind_assoc.
Qed.

#[program]
Instance run_impure_Proper_1 (i : interface) (a : Type)
  : Proper (semantics_eq ==> eq ==> run_effect_eq) (@run_impure i a).

Next Obligation.
  add_morphism_tactic.
  intros sem sem' equ p.
  revert sem sem' equ.
  induction p; intros sem sem' equ.
  + cbn.
    now rewrite equ.
  + repeat rewrite eval_impure_request_then_assoc.
    repeat rewrite run_impure_request_then_assoc.
    specialize H
      with (eval_effect sem e) (exec_effect sem e) (exec_effect sem' e).
    inversion equ; subst.
    specialize next_eq with _ e.
    apply H in next_eq.
    rewrite <- res_eq.
    exact next_eq.
Qed.

#[program]
Instance run_impure_Proper_2 (i : interface) (a : Type)
  : Proper (eq ==> impure_eq ==> run_effect_eq) (@run_impure i a).

Next Obligation.
  add_morphism_tactic.
  intros sem p q equ.
  revert sem.
  induction equ; intros sem.
  + reflexivity.
  + repeat rewrite run_impure_request_then_assoc.
    apply H.
Qed.

#[program]
Instance eval_impure_Proper (i : interface) (a : Type)
  : Proper (semantics_eq ==> impure_eq ==> eq) (@eval_impure i a).

Next Obligation.
  add_morphism_tactic.
  intros sem sem' equ1 p q equ2.
  unfold eval_impure.
  now rewrite equ1, equ2.
Qed.

#[program]
Instance exec_impure_Proper (i : interface) (a : Type)
  : Proper (semantics_eq ==> impure_eq ==> semantics_eq) (@exec_impure i a).

Next Obligation.
  add_morphism_tactic.
  intros sem sem' equ1 p q equ2.
  unfold exec_impure.
  now rewrite equ1, equ2.
Qed.

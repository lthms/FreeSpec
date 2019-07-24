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

From Coq Require Import Setoid Morphisms.
From Prelude Require Import Tactics Equality.
From FreeSpec.Core Require Export Impure.

#[local]
Open Scope prelude_scope.

#[local]
Open Scope signature_scope.

(** * Definition *)

Record specs (i : interface) (Ω : Type) : Type :=
  { witness_update (a : Type) (ω : Ω) : i a -> a -> Ω
  ; requirements (a : Type) (ω : Ω) : i a -> Prop
  ; promises (a : Type) (ω : Ω) : i a -> a -> Prop
  }.

Arguments witness_update [i Ω] (_) [a] (_ _ _).
Arguments requirements [i Ω] (_) [a] (_).
Arguments promises [i Ω] (_) [a] (_ _).

Definition no_req (i : interface) {Ω a} (ω : Ω) (e : i a) : Prop := True.

Definition no_prom {i : interface} {Ω a} (ω : Ω) (e : i a) (x : a) : Prop := True.

Definition no_specs (i : interface) : specs i unit :=
  {| witness_update := fun (a : Type) (u : unit) (e : i a) (x : a) => u
   ; requirements := @no_req i unit
   ; promises := @no_prom i unit
   |}.

Definition specsplus {i j Ωi Ωj} (speci : specs i Ωi) (specj : specs j Ωj)
  : specs (i ⊕ j) (Ωi * Ωj) :=
  {| witness_update := fun (a : Type) (ω : Ωi * Ωj) (e : (i ⊕ j) a) (x : a) =>
                         match e with
                         | in_left e => (witness_update speci (fst ω) e x, snd ω)
                         | in_right e => (fst ω, witness_update specj (snd ω) e x)
                         end
  ;  requirements := fun (a : Type) (ω : Ωi * Ωj) (e : (i ⊕ j) a) =>
                       match e with
                       | in_left e => requirements speci (fst ω) e
                       | in_right e => requirements specj (snd ω) e
                       end
  ;  promises := fun (a : Type) (ω : Ωi * Ωj) (e : (i ⊕ j) a) (x : a) =>
                   match e with
                   | in_left e => promises speci (fst ω) e x
                   | in_right e => promises specj (snd ω) e x
                   end
  |}.

Infix "<.>" := specsplus (at level 77, left associativity) : specs_scope.
Infix "⊙" := specsplus (at level 77, left associativity) : specs_scope.

Bind Scope specs_scope with specs.

(** * Reasoning with Specifications

    ** Impure Computation Trustworthiness

    An impure computation [p] is said trustworthy wrt. a specification [c] in
    accordance to a witness [ω] when it only uses primitives of [i] which
    satisfies [c] requirements. *)

Inductive trustworthy_impure {i a Ω} (c : specs i Ω) (ω : Ω) : impure i a -> Prop :=

(** - Given a term [x], the computation [local x] is always trustworthy wrt. [c]
      in accordance to [ω], since it does not use any primitives. *)
| trustworthy_local (x : a)
  : trustworthy_impure c ω (local x)

(** - Given a primitive [e] and a continuation [f], if

      - [e] satisfies [c] requirements
      - [f] computations are trustworthy wrt. [c] in accordance to [ω'], where
        [ω'] is the witness after [e] interpretation

      then the impure computation [request_then e f] is trustworthy wrt. [c] in
      accordance to [ω]. *)
| trustworthy_request {b}
    (e : i b) (req : requirements c ω e) (f : b -> impure i a)
    (prom : forall (x : b),
        promises c ω e x -> trustworthy_impure c (witness_update c ω e x) (f x))
  : trustworthy_impure c ω (request_then e f).

#[program]
Instance trustworthy_impure_Proper {i Ω} (a : Type) (c : specs i Ω) (ω : Ω)
  : Proper ('equal ==> Basics.impl) (trustworthy_impure (a:=a) c ω).

Next Obligation.
  add_morphism_tactic.
  unfold Basics.impl.
  intros p q equ.
  revert ω.
  induction equ; intros ω.
  + auto.
  + intros trust.
    inversion trust; ssubst.
    constructor.
    ++ exact req.
    ++ intros x p.
       apply H.
       now apply prom.
Qed.

Inductive trustworthy_run {i a Ω} (c : specs i Ω)
  : impure i a -> Ω -> Ω -> a -> Prop :=

(** Given a term [x], and an initial witness [ω], then a trustworthy run of
    [local x] produces a result [x] and a witness state [ω]. *)
| run_local
    (x : a) (ω : Ω)
  : trustworthy_run c (local x) ω ω x

(** Given an initial witness [ω], a primitive [e] which satisfies [c]
    requirements, and a continuation [f], a result [x] for [e] which satisfies
    [c] promises, if we can show that there is a trustworthy run of [f x]
    which produces a term [y] and a witness [ω'], then there is a trustworthy
    run of [request_then e f] which produces a result [y] and a witness [ω']. *)
| run_request {b}
    (ω : Ω)
    (e : i b) (req : requirements c ω e) (f : b -> impure i a)
    (x : b) (prom : promises c ω e x)
    (ω' : Ω) (y : a) (rec : trustworthy_run c (f x) (witness_update c ω e x) ω' y)
  : trustworthy_run c (request_then e f) ω ω' y.

(** Given a specification [c] and a witness [ω] an impure computation [p] and a
    continuation [f] if [p] is a trustworthy program wrt. [c] in accordance to
    [ω] and for all result [x] and witness [ω'] produces by [p], [f x] is
    trustworthy then [local p f] is trustworthy. *)
Lemma trustworthy_bind_trustworthy_run {i a b Ω}
  (c : specs i Ω) (ω : Ω)
  (p : impure i a) (f : a -> impure i b)
  (trust : trustworthy_impure c ω p)
  (run : forall (x : a) (ω' : Ω),
      trustworthy_run c p ω ω' x -> trustworthy_impure c ω' (f x))
  : trustworthy_impure c ω (impure_bind p f).

Proof.
  revert ω trust run.
  induction p; intros ω trust run.
  + apply run.
    constructor.
  + cbn.
    inversion trust; ssubst.
    constructor.
    ++ apply req.
    ++ intros y promx.
       apply H; [ auto |].
       intros z ω' run'.
       apply run.
       econstructor; eauto.
Qed.

Hint Resolve trustworthy_bind_trustworthy_run : freespec_scope.

(** ** Semantics Compliance *)

CoInductive compliant_semantics {i Ω} (c : specs i Ω) : Ω -> semantics i -> Prop :=
| compliant_semantics_rec
(** Given a semantics [sem], and a witness [ω]… *)
    (sem : semantics i) (ω : Ω)
(** … if [sem] computes results which satisfies [c] promises for effects which
    satisfies [c] requirements… *)
    (prom : forall {a} (e : i a),
        requirements c ω e -> promises c ω e (eval_effect sem e))
(** … and if the resulting semantics produces after interpreting [e] complies to
    [c] in accordance to [ω'], where [ω'] is the new witness state after [e]
    interpretation… *)
    (next : forall {a} (e : i a),
        requirements c ω e
        -> compliant_semantics c (witness_update c ω e (eval_effect sem e)) (exec_effect sem e))
(** … then [sem] complies to [c] in accordance to [ω] *)
  : compliant_semantics c ω sem.

Lemma compliant_semantics_requirement_promises {i Ω a} (c : specs i Ω) (ω : Ω)
  (e : i a) (req : requirements c ω e)
  (sem : semantics i) (comp : compliant_semantics c ω sem)
  : promises c ω e (eval_effect sem e).

Proof.
  inversion comp; ssubst.
  now apply prom.
Qed.

Hint Resolve compliant_semantics_requirement_promises : freespec.

Lemma compliant_semantics_requirement_compliant {i Ω a} (c : specs i Ω) (ω : Ω)
  (e : i a) (req : requirements c ω e)
  (sem : semantics i) (comp : compliant_semantics c ω sem)
  : compliant_semantics c (witness_update c ω e (eval_effect sem e)) (exec_effect sem e).

Proof.
  inversion comp; ssubst.
  now apply next.
Qed.

Hint Resolve compliant_semantics_requirement_compliant : freespec.

Lemma compliant_semantics_exec_effect_equ {i Ω a} (c : specs i Ω) (ω : Ω)
  (sem sem' : semantics i) (equ : sem == sem')
  (e : i a)
  : exec_effect sem e == exec_effect sem' e.
Proof.
  inversion equ; ssubst.
  specialize step_equiv with a e.
  now inversion step_equiv; ssubst.
Qed.

Hint Resolve compliant_semantics_exec_effect_equ : freespec.

#[program]
Instance compliant_semantics_Proper {i Ω} (c : specs i Ω) (ω : Ω)
  : Proper ('equal ==> Basics.impl) (compliant_semantics c ω).

Next Obligation.
  add_morphism_tactic.
  revert ω.
  cofix compliant_semantics_Proper; intros ω.
  intros σ σ' equ comp.
  destruct comp.
  constructor.
  + now setoid_rewrite <- equ.
  + intros a e req.
    apply (compliant_semantics_Proper (witness_update c ω e (eval_effect σ' e)) (exec_effect sem e)).
    ++ auto with freespec.
    ++ rewrite <- equ at 1.
       now apply next.
Qed.

Lemma no_specs_compliant_semantics {i}
  (sem : semantics i) (ϵ : unit)
  : compliant_semantics (no_specs i) ϵ sem.

Proof.
  revert sem.
  cofix no_specs_compliant_semantics; intros sem.
  constructor.
  + trivial.
  + intros a e req.
    apply no_specs_compliant_semantics.
Qed.

Hint Resolve no_specs_compliant_semantics : freespec.

Lemma compliant_semantics_semplus {i j Ωi Ωj}
  (semi : semantics i) (semj : semantics j)
  (ci : specs i Ωi) (ωi : Ωi) (compi : compliant_semantics ci ωi semi)
  (cj : specs j Ωj) (ωj : Ωj) (compj : compliant_semantics cj ωj semj)
  : compliant_semantics (ci ⊙ cj) (ωi, ωj) (semi ⊗ semj).

Proof.
  revert ωi ωj semi semj compi compj.
  cofix compliant_semantics_semplus; intros ωi ωj semi semj compi compj.
  constructor; intros a e req.
  + destruct e; [ inversion compi | inversion compj ]; ssubst; now apply prom.
  + destruct e; [ inversion compi | inversion compj ]; ssubst;
      apply compliant_semantics_semplus;
      auto;
      now apply next.
Qed.

Hint Resolve compliant_semantics_semplus : freespec.

Lemma compliant_semantics_semplus_no_specs {i j Ω}
  (ci : specs i Ω) (ω : Ω) (semi : semantics i) (comp : compliant_semantics ci ω semi)
  (semj : semantics j) (ϵ : unit)
  : compliant_semantics (ci ⊙ no_specs j) (ω, ϵ) (semi ⊗ semj).

Proof.
  auto with freespec.
Qed.

#[local]
Fixpoint witness_impure_aux {i Ω a}
  (sem : semantics i) (p : impure i a) (c : specs i Ω) (ω : Ω) : interp_out i a * Ω :=
  match p with
  | local x => (mk_out x sem, ω)
  | request_then e f =>
    let out := run_effect sem e in
    let res := interp_result out in
    witness_impure_aux (interp_next out) (f res) c (witness_update c ω e res)
  end.

Lemma fst_witness_impure_aux_run_impure {i Ω a}
  (sem : semantics i) (p : impure i a) (c : specs i Ω) (ω : Ω)
  : fst (witness_impure_aux sem p c ω) = run_impure sem p.

Proof.
  revert sem ω.
  induction p; intros sem ω.
  + reflexivity.
  + apply H.
Qed.

Hint Rewrite @fst_witness_impure_aux_run_impure : freespec.

Definition witness_impure {i Ω a}
  (sem : semantics i) (p : impure i a) (c : specs i Ω) (ω : Ω) : Ω :=
  snd (witness_impure_aux sem p c ω).

Lemma witness_impure_request_then_equ {i Ω a b} (c : specs i Ω) (ω : Ω)
  (sem : semantics i) (e : i a) (f : a -> impure i b)
  : witness_impure sem (request_then e f) c ω
    = witness_impure (exec_effect sem e)
                     (f (eval_effect sem e))
                     c
                     (witness_update c ω e (eval_effect sem e)).
Proof eq_refl.

Hint Rewrite @witness_impure_request_then_equ : freespec.

Lemma trustworthy_impure_compliant_specs {i Ω a} (c : specs i Ω) (ω : Ω)
  (p : impure i a) (trust : trustworthy_impure c ω p)
  (sem : semantics i) (comp : compliant_semantics c ω sem)
  : compliant_semantics c (witness_impure sem p c ω) (exec_impure sem p).

Proof.
  revert trust sem comp. revert ω.
  induction p; intros ω trust sem comp.
  + exact comp.
  + inversion trust; ssubst.
    autorewrite with freespec.
    apply H; auto with freespec.
Qed.

Hint Resolve trustworthy_impure_compliant_specs : freespec.

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

    We say [c] is correct wrt. [speci] (a specification for [i]) and [specj] (a
    specification for [i]) iff given primitives which satisfy the requirements of
    [speci], [c] will

    - use trustworthy impure computations wrt. [specj]
    - compute results which satisfy [speci] promises, assuming it can rely on a
      semantics of [j] which complies with [specj]

    The two witness states [ωi : Ωi] (for [speci]) and [ωj : Ωj] (for [specj]),
    and [st : s] the internal state of [c] remained implicit in the previous
    sentence.  In practice, we associate them together by means of a dedicated
    predicate [pred].  It is expected that [pred] is an invariant throughout [c]
    life, meaning that as long as [c] computes result for legitimate effects
    (wrt.  [speci] effects, the updated values of [ωi], [ωj] and [st] continue
    to satisfy [pred]. *)
Definition correct_component {i j Ωi Ωj s}
  (c : component i j s)
  (speci : specs i Ωi) (specj : specs j Ωj)
  (pred : Ωi -> s -> Ωj -> Prop) : Prop :=
  forall (ωi : Ωi) (st : s) (ωj : Ωj) (init : pred ωi st ωj)
    (sem : semantics j) (comp : compliant_semantics specj ωj sem)
    (a : Type) (e : i a) (req : requirements speci ωi e),
    trustworthy_impure specj ωj (c a e st)
    /\ promises speci ωi e (fst (eval_impure sem (c a e st)))
    /\ pred (witness_update speci ωi e (fst (eval_impure sem (c a e st))))
            (snd (eval_impure sem (c a e st)))
            (witness_impure sem (c a e st) specj ωj).

(** Once we have proven [c] is correct wrt. to [speci] and [specj] with [pred]
    acting as an invariant throughout [c] life, we show we can derive a
    semantics from [c] with an initial state [st] which complies to [speci] in
    accordance to [ωi] if we use a semantics of [j] which complies to [specj] in
    accordance to [ωj], where [pred ωi st ωj] is satisfied. *)
Lemma correct_component_derives_compliant_semantics {i j Ωi Ωj s}
  (c : component i j s) (speci : specs i Ωi) (specj : specs j Ωj)
  (pred : Ωi -> s -> Ωj -> Prop)
  (correct : correct_component c speci specj pred)
  (ωi : Ωi) (st : s) (ωj : Ωj) (inv : pred ωi st ωj)
  (sem : semantics j) (comp : compliant_semantics specj ωj sem)
  : compliant_semantics speci ωi (derive_semantics c st sem).

Proof.
  revert inv sem comp.
  revert ωi st ωj.
  cofix correct_component_derives_compliant_semantics.
  intros ωi st ωj inv sem comp.
  unfold correct_component in correct.
  specialize (correct ωi st ωj inv sem comp).
  constructor; intros a e req; specialize (correct a e req);
    destruct correct as [trust [pr inv']].
  + apply pr.
  + eapply correct_component_derives_compliant_semantics.
    ++ apply inv'.
    ++ fold (exec_impure sem (c a e st)).
       apply trustworthy_impure_compliant_specs; [| exact comp ].
       apply trust.
Qed.


(** * Tactics *)

From Prelude Require Import Control.

Ltac destruct_if_when :=
  let eq_cond := fresh "Heq_cond" in
  match goal with
  | |- context[when (negb ?B) _] => case_eq B; intros eq_cond; cbn
  | |- context[when ?B _] => case_eq B; intros eq_cond; cbn
  | |- context[if (negb ?B) then _ else _] => case_eq B; intros eq_cond; cbn
  | |- context[if ?B then _ else _] => case_eq B; intros eq_cond; cbn
  | _ => idtac
  end.

Ltac prove_impure :=
  repeat (cbn; destruct_if_when);
  lazymatch goal with
  (* 1st case: nested bind:
       rewrite ((p >>= f) >>= g) into p >>= (λ x, f x >>= g) *)
  | |- trustworthy_impure ?c ?w (impure_bind (impure_bind ?p ?f) ?g) =>
    rewrite (impure_bind_assoc p f g); prove_impure
  (* 2nd case: bind opaque program:
       rely on the correct_run abstraction *)
  | |- trustworthy_impure ?c ?w (impure_bind ?p ?f) =>
    let x := fresh "x" in
    let w := fresh "w" in
    let Hrun := fresh "Hrun" in
    apply trustworthy_bind_trustworthy_run; [| intros x w Hrun;
                                                  prove_impure ]
  (* 3rd case: request constructor
      generate a gool to prove the effect satisfies the precondition *)
  | |- trustworthy_impure ?c ?w (request_then ?e ?f) =>
    let Hpre := fresh "Hpre" in
    assert (Hpre: requirements c w e); [| constructor; [apply Hpre |];
                                          let sig := fresh "sig" in
                                          let Hsig := fresh "Hsig" in
                                          let res := fresh "res" in
                                          let Hpost := fresh "Hpost" in
                                          intros res Hpost;
                                          prove_impure ]
  (* 4st case: pure constructor
       conclude *)
  | |- trustworthy_impure ?c ?w (local ?x) => constructor
  | |- trustworthy_impure ?c ?w (impure_pure ?x) => constructor
  | _ => fail "Unexpected goal: prove_program allows for proving program correctness"
  end.

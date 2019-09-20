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

(** In this library, we provide the necessary material to reason about FreeSpec
    component both in isolation, and in composition.  To do that, we focus our
    reasoning principle on interfaces, by defining how their primitives shall be
    used in the one hand, and what to expect the result computed by “good”
    operational semantics (according to a certain definition of “good”). *)

From Coq Require Import Setoid Morphisms.
From Prelude Require Import Tactics Equality Control.
From FreeSpec.Core Require Export Impure.

Generalizable All Variables.

#[local]
Open Scope prelude_scope.
#[local]
Open Scope signature_scope.

(** * Definition *)

(** A specification dedicated to [i : interface] primilarly provide two
    predicates [requirements] and [promises].

    - [requirements] distinguishes between primitives that can be used (by an
      impure computation), and primitives that cannot be used.
    - [promises] specifies which guarantee can be expected from primitives
      results, as computed by a “good” operational semantics.

    Both [requirements] and [promises] models properties that may vary in time,
    e.g., a primitive may be forbiden at a given time, but authorized later.  To
    take this possibility into account, specifications are parameterized by what
    we have called a “witness.”  A witness is a term which describes the
    necessary information of the past, and allows for taking decision for the
    present.  It can be seen as an abstraction of the concrete state of the
    interface implementer.

    To keep this state up-to-date after each primitive interpretation,
    specifications also defines a dedicated function [witness_update]. *)

Record specs (i : interface) (Ω : Type) : Type :=
  { witness_update (ω : Ω) : forall (a : Type), i a -> a -> Ω
  ; requirements (ω : Ω) : forall (a : Type),  i a -> Prop
  ; promises (ω : Ω) : forall (a : Type), i a -> a -> Prop
  }.

Arguments witness_update [i Ω] (s ω) [a] (_ _).
Arguments requirements [i Ω] (s ω) [a] (_).
Arguments promises [i Ω] (s ω) [a] (_ _).

(** The most simple specification we can define is the one that requires
    anything both for the impure computations which uses the primitives of a
    given interface, and for the operational semantics which compute results for
    these primitives. *)

Definition const_witness {i} :=
  fun (u : unit) (a : Type) (e : i a) (x : a) => u.

Definition no_req {i Ω} (ω : Ω) (a : Type) (e : i a) : Prop := True.

Definition no_prom {i Ω} (ω : Ω) (a : Type) (e : i a) (x : a) : Prop := True.

Definition no_specs (i : interface) : specs i unit :=
  {| witness_update := const_witness
   ; requirements := no_req
   ; promises := no_prom
   |}.

(** A similar —and as simple— specification is the one that forbids the use of a
    given interface. *)

Definition no_use {i Ω} (ω : Ω) (a : Type) (e : i a) : Prop := False.

Definition forbid_specs (i : interface) : specs i unit :=
  {| witness_update := const_witness
   ; requirements := no_use
   ; promises := no_prom
   |}.

(** As we compose interfaces and operational semantics, we can easily compose
    specifications together, by means of the [specsplus] operator (denoted by
    [<.>] or [⊙]). Given [i : interface] and [j : interface], if we can reason
    about [i] and [j] independently (e.g., the requirements of [j] do not vary
    when we use [i]), then we can compose [speci : specs i Ωi] and [specj :
    specs j Ωj], such that [speci ⊙ specj] in a specification for [i ⊕ j]. *)

Definition gen_witness_update `{MayProvide ix i} {Ω a} (c : specs i Ω)
    (ω :  Ω) (e : ix a) (x : a)
  : Ω :=
  match unlift_eff e with
  | Some e => witness_update c ω e x
  | None => ω
  end.

Definition gen_requirements `{MayProvide ix i} {Ω a} (c : specs i Ω)
    (ω :  Ω) (e : ix a)
  : Prop :=
  match unlift_eff e with
  | Some e => requirements c ω e
  | None => True
  end.

Definition gen_promises `{MayProvide ix i} {Ω a} (c : specs i Ω)
    (ω :  Ω) (e : ix a) (x : a)
  : Prop :=
  match unlift_eff e with
  | Some e => promises c ω e x
  | None => True
  end.

Definition specsplus `{Provide ix i, Provide ix j} {Ωi Ωj} (speci : specs i Ωi) (specj : specs j Ωj)
  : specs ix (Ωi * Ωj) :=
  {| witness_update := fun (ω : Ωi * Ωj) (a : Type) (e : ix a) (x : a) =>
                         (gen_witness_update speci (fst ω) e x, gen_witness_update specj (snd ω) e x)
  ;  requirements := fun (ω : Ωi * Ωj) (a : Type) (e : ix a) =>
                       gen_requirements speci (fst ω) e /\ gen_requirements specj (snd ω) e
  ;  promises := fun (ω : Ωi * Ωj) (a : Type) (e : ix a) (x : a) =>
                   gen_promises speci (fst ω) e x /\ gen_promises specj (snd ω) e x
  |}.

Declare Scope specs_scope.

Infix "<.>" := specsplus (at level 77, left associativity) : specs_scope.
Infix "⊙" := specsplus (at level 77, left associativity) : specs_scope.

Bind Scope specs_scope with specs.

(** Finally, and as an example, we define a specification for the interface
    [STORE s] we discuss in [FreeSpec.Core.Impure].  As a reminder, the
    interface is defined as follows:

<<
Inductive STORE (s : Type) : interface :=
| Get : STORE s s
| Put (x : s) : STORE s unit.
>>

    For [STORE s], the best witness is the actuall value of the mutable
    variable.  Therefore, the specification for [STORE s] may be [specs (STORE
    s) s], and the witness will be updated after each [Put] call. *)

Definition store_update (s : Type) :=
  fun (x : s) (a : Type) (e : STORE s a) (_ : a) =>
    match e with
    | Get => x
    | Put x' => x'
    end.

(** Assuming the mutable variable is being initialized prior to any impure
    computation interpretation, we do not have any requirements over the use of
    [STORE s] primitives.  We will get back to this assertion once we have
    defined our specification, but in the meantime, we define its promises.

    The logic of these promises is as follows: [Get] is expected to produce a
    result strictly equal to the witness, and we do not have any promises about
    the result of [Put] (which belongs to [unit] anyway, so there is not much to
    tell). *)

Inductive store_prom (s : Type) (x : s) : forall (a : Type), STORE s a -> a -> Prop :=
| get_prom (x' : s) (equ : x = x') : store_prom s x s Get x'
| put_prom (x' : s) (b : unit) : store_prom s x unit (Put x') b.

(** The actual specification can therefore be defined as follows: *)

Definition store_specs (s : Type) : specs (STORE s) s :=
  {| witness_update := store_update s
  ;  requirements := no_req
  ;  promises := store_prom s
  |}.

(** Now, as we briefly mentionned, this specification allows for reasoning about
    an impure computation which uses the [STORE s] interface, assuming the
    mutable, global variable has been initialized.  We can define another
    specification that do not rely on such assumption, and on the contrary,
    requires an impure computation to initialize the variable prior to using it.

    In this context, the witness can solely be a boolean which tells if the
    variable has been initialized, and the [requirements] will require the
    witness to be [true] to authorize a call of [Get].

    This is one of the key benefit of the FreeSpec approach: because the
    specifications are defined independently from impure computation and
    interfaces, we can actually define several specifications to consider
    different set of hypotheses. *)

(** * Reasoning with Specifications

    ** Impure Computation Trustworthiness

    An impure computation [p] is said trustworthy wrt. a specification [c] in
    accordance to a witness [ω] when it only uses primitives of [i] which
    satisfies [c] requirements. *)

Inductive trustworthy_impure `{MayProvide ix i} {a Ω} (c : specs i Ω) (ω : Ω) : impure ix a -> Prop :=

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

| trustworthy_request_some {b}
    (e : ix b) (f : b -> impure ix a)
    (req : gen_requirements c ω e)
    (prom : forall (x : b),
        gen_promises c ω e x
        -> trustworthy_impure c (gen_witness_update c ω e x) (f x))
  : trustworthy_impure c ω (request_then e f).

#[program]
Instance trustworthy_impure_Proper `{MayProvide ix i} {Ω} (a : Type) (c : specs i Ω) (ω : Ω)
  : Proper (@equal (impure ix a) _ ==> Basics.impl) (trustworthy_impure (a:=a) c ω).

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
    ++ intros x q.
       apply H0.
       now apply prom.
Qed.

(** As is, the definition of [trustworthy_impure] would force FreeSpec users to
    unfold any impure computations they may combine together with [bind].  For
    instance, proving a computation of the form [bind p (λ _, p)] is trustworthy
    would require to prove [p] is trustworthy twice, for two different
    witnesses.  Moreover, it could be challenging to know, when interactively
    writing the proof script, when “the first [p]” stops, and when “the second
    [p]” starts.

    We need a way to compose proofs about impure computations the same way we
    compose impure computations with [bind].  We do that with the
    [trustworthy_run] predicate, which describes the potential outcomes of a
    computation in terms of results and witnesses. *)

Inductive trustworthy_run `{MayProvide ix i} {a Ω} (c : specs i Ω)
  : impure ix a -> Ω -> Ω -> a -> Prop :=

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
    (e : ix b) (req : gen_requirements c ω e) (f : b -> impure ix a)
    (x : b) (prom : gen_promises c ω e x)
    (ω' : Ω) (y : a) (rec : trustworthy_run c (f x) (gen_witness_update c ω e x) ω' y)
  : trustworthy_run c (request_then e f) ω ω' y.

(** Given a specification [c] and a witness [ω] an impure computation [p] and a
    continuation [f] if

    - [p] is a trustworthy impure computation wrt. [c] in accordance to [ω]
    - for all result [x] and witness [ω'] produces by [p], [f x] is trustworthy


    Then [bind p f] is trustworthy. *)

Lemma trustworthy_bind_trustworthy_run `{MayProvide ix i} {a b Ω}
  (c : specs i Ω) (ω : Ω)
  (p : impure ix a) (f : a -> impure ix b)
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
       apply H0; [ auto |].
       intros z ω' run'.
       apply run.
       econstructor; eauto.
Qed.

Hint Resolve trustworthy_bind_trustworthy_run : freespec_scope.

Lemma trustworthy_bind_exists_trustworthy_run `{MayProvide ix i} {a b Ω}
    (c : specs i Ω) (ω ω' : Ω)
    (p : impure ix a) (f : a -> impure ix b) (x : b)
    (trust : trustworthy_run c (impure_bind p f) ω ω' x)
  : exists (ω'' : Ω) (y : a),
    trustworthy_run c p ω ω'' y /\ trustworthy_run c (f y) ω'' ω' x.

Proof.
  revert trust.
  revert ω ω'.
  induction p; intros ω ω' trust.
  + exists ω; exists x0.
    split.
    ++ constructor.
    ++ exact trust.
  + inversion trust; ssubst.
    apply H0 in rec.
    destruct rec as [ω'' [y [trust1 trust2]]].
    exists ω''; exists y.
    split; auto.
    constructor 2 with (x := x0); auto.
Qed.

(** ** Semantics Compliance *)

(** Given a semantics [sem], and a witness [ω] if [sem] computes results which
    satisfies [c] promises for effects which satisfies [c] requirements and if
    the resulting semantics produces after interpreting [e] complies to [c] in
    accordance to [ω'], where [ω'] is the new witness state after [e]
    interpretation then [sem] complies to [c] in accordance to [ω] *)

CoInductive compliant_semantics `{MayProvide ix i} {Ω} (c : specs i Ω) : Ω -> semantics ix -> Prop :=
| compliant_semantics_rec
    (sem : semantics ix) (ω : Ω)
    (prom : forall {a} (e : ix a),
        gen_requirements c ω e -> gen_promises c ω e (eval_effect sem e))
    (next : forall {a} (e : ix a),
        gen_requirements c ω e
        -> compliant_semantics c (gen_witness_update c ω e (eval_effect sem e)) (exec_effect sem e))
  : compliant_semantics c ω sem.

(** Proving that semantics obtained from the [store] function are compliant with
    [store_specs] is relatively simple. *)

Lemma store_complies_to_store_specs {s} (st : s)
  : compliant_semantics (store_specs s) st (store st).

Proof.
  revert st; cofix compliant_semantics_rec; intros st.
  constructor.
  + intros a [|st'] _.
    ++ now constructor.
    ++ now constructor.
  + intros a e req.
    cbn.
    assert (R : exec_effect (store st) e = store (store_update s st a e (eval_effect (store st) e)))
      by now destruct e as [|st'].
    rewrite R.
    apply compliant_semantics_rec.
Qed.

Lemma compliant_semantics_requirement_promises `{MayProvide ix i} {Ω a} (c : specs i Ω) (ω : Ω)
  (e : ix a) (req : gen_requirements c ω e)
  (sem : semantics ix) (comp : compliant_semantics c ω sem)
  : gen_promises c ω e (eval_effect sem e).

Proof.
  inversion comp; ssubst.
  now apply prom.
Qed.

Hint Resolve compliant_semantics_requirement_promises : freespec.

Lemma compliant_semantics_requirement_compliant `{MayProvide ix i} {Ω a} (c : specs i Ω) (ω : Ω)
  (e : ix a) (req : gen_requirements c ω e)
  (sem : semantics ix) (comp : compliant_semantics c ω sem)
  : compliant_semantics c (gen_witness_update c ω e (eval_effect sem e)) (exec_effect sem e).

Proof.
  inversion comp; ssubst.
  now apply next.
Qed.

Hint Resolve compliant_semantics_requirement_compliant : freespec.

Lemma compliant_semantics_exec_effect_equ `{MayProvide ix i} {Ω a} (c : specs i Ω) (ω : Ω)
  (sem sem' : semantics ix) (equ : sem == sem')
  (e : ix a)
  : exec_effect sem e == exec_effect sem' e.
Proof.
  inversion equ; ssubst.
  specialize step_equiv with a e.
  now inversion step_equiv; ssubst.
Qed.

Hint Resolve compliant_semantics_exec_effect_equ : freespec.

#[program]
Instance compliant_semantics_Proper `{MayProvide ix i} {Ω} (c : specs i Ω) (ω : Ω)
  : Proper (@equal (semantics ix) _ ==> Basics.impl) (compliant_semantics c ω).

Next Obligation.
  add_morphism_tactic.
  revert ω.
  cofix compliant_semantics_Proper; intros ω.
  intros σ σ' equ comp.
  destruct comp.
  constructor.
  + now setoid_rewrite <- equ.
  + intros a e req.
    apply (compliant_semantics_Proper (gen_witness_update c ω e (eval_effect σ' e)) (exec_effect sem e)).
    ++ auto with freespec.
    ++ rewrite <- equ at 1.
       now apply next.
Qed.

Lemma no_specs_compliant_semantics `{MayProvide ix i}
  (sem : semantics ix) (ϵ : unit)
  : compliant_semantics (no_specs i) ϵ sem.

Proof.
  revert sem.
  cofix no_specs_compliant_semantics; intros sem.
  constructor.
  + trivial.
  + intros a e req.
    unfold gen_witness_update.
    destruct (unlift_eff e); [ apply no_specs_compliant_semantics | auto ].
Qed.

Hint Resolve no_specs_compliant_semantics : freespec.

#[local]
Fixpoint witness_impure_aux `{MayProvide ix i} {Ω a}
  (sem : semantics ix) (p : impure ix a) (c : specs i Ω) (ω : Ω) : interp_out ix a * Ω :=
  match p with
  | local x => (mk_out x sem, ω)
  | request_then e f =>
    let out := run_effect sem e in
    let res := interp_result out in
    witness_impure_aux (interp_next out) (f res) c (gen_witness_update c ω e res)
  end.

#[program]
Instance witness_impure_aux_Proper_2 `{MayProvide ix i} {Ω a}
  : Proper (eq ==> 'equal ==> eq ==> eq ==> eq) (@witness_impure_aux ix i _ Ω a).

Next Obligation.
  add_morphism_tactic.
  intros sem p q equp c ω.
  revert sem ω.
  induction equp; intros sem ω.
  + reflexivity.
  + cbn.
    apply H0.
Qed.

Lemma fst_witness_impure_aux_run_impure `{MayProvide ix i} {Ω a}
  (sem : semantics ix) (p : impure ix a) (c : specs i Ω) (ω : Ω)
  : fst (witness_impure_aux sem p c ω) = run_impure sem p.

Proof.
  revert sem ω.
  induction p; intros sem ω.
  + reflexivity.
  + apply H0.
Qed.

Hint Rewrite @fst_witness_impure_aux_run_impure : freespec.

Definition witness_impure `{MayProvide ix i} {Ω a}
  (sem : semantics ix) (p : impure ix a) (c : specs i Ω) (ω : Ω) : Ω :=
  snd (witness_impure_aux sem p c ω).

#[program]
Instance witness_impure_Proper `{MayProvide ix i} {Ω a}
  : Proper (eq ==> 'equal ==> eq ==> eq ==> eq) (@witness_impure ix i _ Ω a).

Next Obligation.
  add_morphism_tactic.
  unfold witness_impure.
  intros sem p q equp c ω.
  now rewrite equp.
Qed.

Lemma compliant_semantics_trustworthy_impure_gives_trustworthy_run `{MayProvide ix i} {Ω a}
  (c : specs i Ω) (ω : Ω) (p : impure ix a) (trust : trustworthy_impure c ω p)
  (sem : semantics ix) (comp : compliant_semantics c ω sem)
  : trustworthy_run c p ω (witness_impure sem p c ω) (eval_impure sem p).

Proof.
  revert sem comp trust. revert ω.
  induction p; intros ω sem comp trust.
  + constructor.
  + inversion trust; ssubst.
    inversion comp; ssubst.
    econstructor; auto.
    apply H0.
    ++ now apply next.
    ++ inversion trust; ssubst.
       apply prom1.
       now apply prom0.
Qed.

Hint Resolve compliant_semantics_trustworthy_impure_gives_trustworthy_run : freespec.

Lemma witness_impure_request_then_equ `{MayProvide ix i} {Ω a b} (c : specs i Ω) (ω : Ω)
  (sem : semantics ix) (e : ix a) (f : a -> impure ix b)
  : witness_impure sem (request_then e f) c ω
    = witness_impure (exec_effect sem e)
                     (f (eval_effect sem e))
                     c
                     (gen_witness_update c ω e (eval_effect sem e)).
Proof eq_refl.

Hint Rewrite @witness_impure_request_then_equ : freespec.

Lemma trustworthy_impure_compliant_specs `{MayProvide ix i} {Ω a} (c : specs i Ω) (ω : Ω)
  (p : impure ix a) (trust : trustworthy_impure c ω p)
  (sem : semantics ix) (comp : compliant_semantics c ω sem)
  : compliant_semantics c (witness_impure sem p c ω) (exec_impure sem p).

Proof.
  revert trust sem comp. revert ω.
  induction p; intros ω trust sem comp.
  + exact comp.
  + inversion trust; ssubst.
    autorewrite with freespec.
    apply H0; auto with freespec.
Qed.

Hint Resolve trustworthy_impure_compliant_specs : freespec.

Lemma gen_promises_equ {a Ωi Ωj} `{Provide ix i} `{Provide ix j}
    (ci : specs i Ωi) (ωi : Ωi)
    (cj : specs j Ωj) (ωj : Ωj)
    (e : ix a) (x : a)
  : gen_promises ci ωi e x /\ gen_promises cj ωj e x
    <-> gen_promises (ci ⊙ cj) (ωi, ωj) e x.

Proof.
  split; auto.
Qed.

Lemma gen_requirements_equ {a Ωi Ωj} `{Provide ix i} `{Provide ix j}
    (ci : specs i Ωi) (ωi : Ωi) (cj : specs j Ωj) (ωj : Ωj) (e : ix a)
  : gen_requirements ci ωi e /\ gen_requirements cj ωj e
    <-> gen_requirements (ci ⊙ cj) (ωi, ωj) e.

Proof.
  split; auto.
Qed.

Lemma trustworthy_impure_generalize `{Provide ix i} `{Provide ix j} {a Ωi Ωj}
    (p : impure ix a)
    (speci : specs i Ωi) (ωi : Ωi) (specj : specs j Ωj) (ωj : Ωj)
  : trustworthy_impure speci ωi p
    -> trustworthy_impure specj ωj p
    -> trustworthy_impure (speci ⊙ specj) (ωi, ωj) p.

Proof.
  revert ωi ωj.
  induction p; intros ωi ωj.
  + intros.
    constructor.
  + intros trust trust'.
    inversion trust; ssubst.
    inversion trust'; ssubst.
    constructor.
    ++ rewrite <- gen_requirements_equ.
       now split.
    ++ intros x gen_prom.
       rewrite <- gen_promises_equ in gen_prom.
       apply H3; [ apply prom | apply prom0 ]; apply gen_prom.
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

Definition correct_component {i jx Ωi Ωj}
  (c : component i jx) `{MayProvide jx j}
  (speci : specs i Ωi) (specj : specs j Ωj)
  (pred : Ωi -> Ωj -> Prop) : Prop :=
  forall (ωi : Ωi) (ωj : Ωj) (init : pred ωi ωj)
    (a : Type) (e : i a) (req : requirements speci ωi e),
    trustworthy_impure specj ωj (c a e) /\
    forall (x : a) (ωj' : Ωj)
      (run : trustworthy_run specj (c a e) ωj ωj' x),
      promises speci ωi e x /\ pred (witness_update speci ωi e x) ωj'.

(** Once we have proven [c] is correct wrt. to [speci] and [specj] with [pred]
    acting as an invariant throughout [c] life, we show we can derive a
    semantics from [c] with an initial state [st] which complies to [speci] in
    accordance to [ωi] if we use a semantics of [j] which complies to [specj] in
    accordance to [ωj], where [pred ωi st ωj] is satisfied. *)

Lemma trustworthy_impure_compliant_specs_trustworthy_run `{MayProvide ix i} {a Ω}
    (spec : specs i Ω) (ω : Ω)
    (sem : semantics ix) (comp : compliant_semantics spec ω sem)
    (p : impure ix a) (trust : trustworthy_impure spec ω p)
  : trustworthy_run spec p ω (witness_impure sem p spec ω) (eval_impure sem p).

Proof.
  revert ω sem comp trust.
  induction p; intros ω sem comp trust.
  + constructor.
  +  inversion trust; ssubst.
     constructor 2 with (x := eval_effect sem e).
     ++ exact req.
     ++ auto with freespec.
     ++ change (witness_impure sem (request_then e f) spec ω)
          with (witness_impure (exec_effect sem e) (f (eval_effect sem e)) spec
                               (gen_witness_update spec ω e (eval_effect sem e))).
        change (eval_impure sem (request_then e f))
          with (eval_impure (exec_effect sem e) (f (eval_effect sem e))).
        apply H0;
          auto with freespec.
Qed.

Lemma correct_component_derives_compliant_semantics `{MayProvide jx j} {i Ωi Ωj}
  (c : component i jx) (speci : specs i Ωi) (specj : specs j Ωj)
  (pred : Ωi -> Ωj -> Prop)
  (correct : correct_component c speci specj pred)
  (ωi : Ωi) (ωj : Ωj) (inv : pred ωi ωj)
  (sem : semantics jx) (comp : compliant_semantics specj ωj sem)
  : compliant_semantics speci ωi (derive_semantics c sem).

Proof.
  revert ωi ωj inv sem comp.
  cofix correct_component_derives_compliant_semantics.
  intros ωi ωj inv sem comp.
  unfold correct_component in correct.
  specialize (correct ωi ωj inv).
  constructor; intros a e req; specialize (correct a e req);
    destruct correct as [trust run].
    specialize run with (eval_impure sem (c a e))
                        (witness_impure (H := H) sem (c a e) specj ωj).
  + apply run.
    auto with freespec.
  + eapply correct_component_derives_compliant_semantics.
    ++ apply run.
       apply trustworthy_impure_compliant_specs_trustworthy_run; auto.
    ++ fold (exec_impure sem (c a e)).
       auto with freespec.
Qed.

(** * Tactics *)

(** The [impure] monad is an empty shell which brings structure and only
    that.  It is not relevant when it comes to verifying impure computations,
    and we provide a tactic called [prove_impure] to erase it while proving a
    given impure computation is trustworthy wrt. to a given specification. *)

Ltac destruct_if_when :=
  let equ_cond := fresh "equ_cond" in
  match goal with
  | |- context[when (negb ?B) _] => case_eq B; intros equ_cond; cbn
  | |- context[when ?B _] => case_eq B; intros equ_cond; cbn
  | |- context[if (negb ?B) then _ else _] => case_eq B; intros equ_cond; cbn
  | |- context[if ?B then _ else _] => case_eq B; intros equ_cond; cbn
  | _ => idtac
  end.

Ltac destruct_if_when_in hyp :=
  let equ_cond := fresh "equ" in
  match type of hyp with
  | context[when (negb ?B) _] => case_eq B;
                                 intro equ_cond;
                                 rewrite equ_cond in hyp
  | context[when ?B _] => case_eq B;
                          intro equ_cond;
                          rewrite equ_cond in hyp
  | context[if (negb ?B) then _ else _] => case_eq B;
                                           intro equ_cond;
                                           rewrite equ_cond in hyp
  | context[if ?B then _ else _] => case_eq B;
                                    intro equ_cond;
                                    rewrite equ_cond in hyp
  | _ => idtac
  end.

Ltac prove_impure :=
  repeat (cbn -[gen_requirements gen_promises gen_witness_update]; destruct_if_when);
  lazymatch goal with

  | H : ?a |- ?a => exact H

  | |- _ /\ _ => split; prove_impure
  | H : _ /\ _ |- _ => destruct H; prove_impure
  | H : True |- _ => clear H; prove_impure

  | |- context[gen_witness_update _ _ _ _] =>
    unfold gen_witness_update;
    repeat (rewrite unlift_lift_equ || rewrite distinguish);
    prove_impure

  | H : context[gen_witness_update _ _ _ _] |- _ =>
    unfold gen_witness_update in H;
    repeat (rewrite unlift_lift_equ in H || rewrite distinguish in H);
    prove_impure

  | |- trustworthy_impure ?c ?w (impure_bind (impure_bind ?p ?f) ?g) =>
    rewrite (impure_bind_assoc p f g);
    prove_impure

  | |- trustworthy_impure ?c ?w (impure_bind ?p ?f) =>
    let x := fresh "x" in
    let w := fresh "w" in
    let Hrun := fresh "Hrun" in
    apply trustworthy_bind_trustworthy_run; [| intros x w Hrun;
                                               prove_impure ]


  | |- trustworthy_impure _ _ (local _) => constructor
  | |- trustworthy_impure _ _ (impure_pure _) => constructor

  | |- trustworthy_impure ?c ?w ?p =>
    let p := (eval compute -[lift_eff unlift_eff] in p) in
    match p with
    | request_then _ _ =>
      let req := fresh "req" in
      assert (req : gen_requirements c w p); [ prove_impure
                                             | constructor; prove_impure
                                             ]
    | _ => idtac
    end
  | |- context[gen_requirements _ _ _] =>
    unfold gen_requirements;
    repeat (rewrite unlift_lift_equ || rewrite distinguish);
    prove_impure
  | H: context[gen_requirements _ _ _] |- _ =>
    cbn in H;
    unfold gen_requirements in H;
    repeat (rewrite unlift_lift_equ in H || rewrite distinguish in H);
    prove_impure

  | |- forall _, gen_promises _ _ _ _ -> _ =>
    let x := fresh "x" in
    let prom := fresh "prom" in
    intros x prom;
    cbn in prom;
    unfold gen_promises in prom;
    repeat (rewrite unlift_lift_equ in prom || rewrite distinguish in prom);
    prove_impure

  | |- ?a => auto
  end.

(*
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
    assert (Hpre: gen_requirements c w e); [ unfold gen_requirements;
                                             try rewrite unlift_lift_equ
                                           | constructor; [apply Hpre |];
                                             unfold gen_requirements in Hpre;
                                             let sig := fresh "sig" in
                                             let Hsig := fresh "Hsig" in
                                             let res := fresh "res" in
                                             let Hpost := fresh "Hpost" in
                                             unfold gen_witness_update;
                                             unfold gen_promises;
                                             try rewrite unlift_lift_equ in Hpre;
                                             try rewrite unlift_lift_equ;
                                             intros res Hpost;
                                             prove_impure ]
  (* 4st case: pure constructor
       conclude *)
  | |- trustworthy_impure ?c ?w (local ?x) => constructor
  | |- trustworthy_impure ?c ?w (impure_pure ?x) => constructor
  | |- trustworthy_impure ?c ?w (request ?x) => unfold request; prove_impure
  | |- trustworthy_impure ?c ?w ?p => idtac
  | |- _ => fail "prove_impure aims to prove impure computation trustworthiness"
  end.
*)

Ltac simpl_gens :=
  cbn in *;
  repeat lazymatch goal with
         | H : gen_requirements _ _ _ /\ gen_requirements _ _ _ |- _ =>
           destruct H
         | H : gen_promises _ _ _ _ /\ gen_promises _ _ _ _ |- _ =>
           destruct H
         end;
  repeat unfold gen_requirements in *;
  repeat unfold gen_promises in *;
  repeat unfold gen_witness_update in *;
  repeat
    lazymatch goal with
    | H : context[unlift_eff (lift_eff ?e)] |- _ =>
      (rewrite unlift_lift_equ in H || rewrite distinguish in H);
      cbn in H
    | |- context[unlift_eff (lift_eff ?e)] =>
      (rewrite unlift_lift_equ || rewrite distinguish); cbn
    end;
  repeat
    lazymatch goal with
    | H : True |- _ => clear H
    end.

Ltac unroll_impure_run_aux run :=
  repeat (cbn -[gen_witness_update gen_requirements gen_promises] in run; destruct_if_when_in run);
  lazymatch type of run with

  | trustworthy_run _ (impure_pure _) _ _ _ =>
    inversion run; ssubst; clear run
  | trustworthy_run _ (local _) _ _ _ =>
    inversion run; ssubst; clear run

  | trustworthy_run ?specs (request_then ?e ?f) ?init ?final ?res =>
    inversion run; ssubst;
    clear run;
    lazymatch goal with
    | next : trustworthy_run specs _ _ final res |- _ =>
    (* | next : trustworthy_run specs _ (gen_witness_update specs _ e _) _ _ |- _ => *)
      unroll_impure_run_aux next
    | |- _ => fail "unexpected error, consider reporting the issue"
    end

  | trustworthy_run ?specs (impure_bind (impure_bind ?p ?f) ?g) ?init ?final ?res =>
    rewrite (impure_bind_assoc p f g) in run;
    unroll_impure_run_aux run

  | trustworthy_run ?specs (impure_bind ?p ?f) ?init ?final ?res =>
    apply (trustworthy_bind_exists_trustworthy_run specs init final p f res) in run;
    let run1 := fresh "run" in
    let run2 := fresh "run" in
    destruct run as [?ω'' [?y [run1 run2]]];
    unroll_impure_run_aux run1; unroll_impure_run_aux run2

  | trustworthy_run ?specs ?p ?init ?final ?res =>
    lazymatch (eval compute -[lift_eff] in p) with
    | request_then ?e ?f =>
      inversion run; ssubst;
      clear run;
      lazymatch goal with
      | next : trustworthy_run specs _ _ final res |- _ =>
        unroll_impure_run_aux next
      | |- _ => idtac specs init e final res
      end
    | _ => idtac
    end

  | ?e => fail "cannot handle goal of the form" e
  end.

Ltac unroll_impure_run run := unroll_impure_run_aux run; simpl_gens.

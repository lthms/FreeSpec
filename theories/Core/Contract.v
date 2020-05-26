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
    components both in isolation, and in composition.  To do that, we focus our
    reasoning principles on interfaces, by defining how their primitives shall
    be used, and what to expect the result computed by “correct” operational
    semantics (according to a certain definition of “correct”). *)

From Coq Require Import Setoid Morphisms.
From FreeSpec.Core Require Export Interface Impure Semantics Component.

#[local]
Open Scope signature_scope.

(** * Definition *)

(** A contract dedicated to [i : interface] primarily provides two
    predicates.

    - [caller_obligation] distinguishes between primitives that can be used (by
      an impure computation), and primitives that cannot be used.
    - [callee_obligation] specifies which guarantees can be expected from
      primitives results, as computed by a “good” operational semantics.

    Both [caller_obligation] and [callee_obligation] model properties that may
    vary in time, e.g., a primitive may be forbidden at a given time, but
    authorized later.  To take this possibility into account, contracts are
    parameterized by what we have called a “witness.”  A witness is a term which
    describes the necessary information of the past, and allows for taking
    decision for the present.  It can be seen as an abstraction of the concrete
    state of the interface implementor.

    To keep this state up-to-date after each primitive interpretation,
    contracts also define a dedicated function [witness_update]. *)

Record contract (i : interface) (Ω : Type) : Type := make_contract
  { witness_update (ω : Ω) : forall (α : Type), i α -> α -> Ω
  ; caller_obligation (ω : Ω) : forall (α : Type),  i α -> Prop
  ; callee_obligation (ω : Ω) : forall (α : Type), i α -> α -> Prop
  }.

Declare Scope contract_scope.
Bind Scope contract_scope with contract.

Arguments make_contract [i Ω] (_ _ _).
Arguments witness_update [i Ω] (c ω) [α] (_ _).
Arguments caller_obligation [i Ω] (c ω) [α] (_).
Arguments callee_obligation [i Ω] (c ω) [α] (_ _).

(** The most simple contract we can define is the one that requires
    anything both for the impure computations which uses the primitives of a
    given interface, and for the operational semantics which compute results for
    these primitives. *)

Definition const_witness {i} :=
  fun (u : unit) (α : Type) (e : i α) (x : α) => u.

Definition no_caller_obligation {i Ω} (ω : Ω) (α : Type) (e : i α) : Prop := True.

Definition no_callee_obligation {i Ω} (ω : Ω) (α : Type) (e : i α) (x : α) : Prop := True.

Definition no_contract (i : interface) : contract i unit :=
  {| witness_update := const_witness
   ; caller_obligation := no_caller_obligation
   ; callee_obligation := no_callee_obligation
   |}.

(** A similar — and as simple — contract is the one that forbids the use of a
    given interface. *)

Definition do_no_use {i Ω} (ω : Ω) (α : Type) (e : i α) : Prop := False.

Definition forbid_specs (i : interface) : contract i unit :=
  {| witness_update := const_witness
   ; caller_obligation := do_no_use
   ; callee_obligation := no_callee_obligation
   |}.

(** As we compose interfaces and operational semantics, we can easily compose
    contracts together, by means of the [cplus] operator. Given [i] and [j]
    two interfaces, if we can reason about [i] and [j] independently (e.g., the
    caller obligations of [j] do not vary when we use [i]), then we can compose
    [ci : contract i Ωi] and [cj : contract j Ωj], such that [cplus ci cj] in a
    contract for [i + j]. *)

Definition gen_witness_update `{MayProvide ix i} {Ω α} (c : contract i Ω)
    (ω :  Ω) (e : ix α) (x : α)
  : Ω :=
  match proj_p e with
  | Some e => witness_update c ω e x
  | None => ω
  end.

Definition gen_caller_obligation `{MayProvide ix i} {Ω α} (c : contract i Ω)
    (ω :  Ω) (e : ix α)
  : Prop :=
  match proj_p e with
  | Some e => caller_obligation c ω e
  | None => True
  end.

Definition gen_callee_obligation `{MayProvide ix i} {Ω α} (c : contract i Ω)
    (ω :  Ω) (e : ix α) (x : α)
  : Prop :=
  match proj_p e with
  | Some e => callee_obligation c ω e x
  | None => True
  end.

Definition cplus `{Provide ix i, Provide ix j} {Ωi Ωj}
    (ci : contract i Ωi) (cj : contract j Ωj)
  : contract ix (Ωi * Ωj) :=
  {| witness_update := fun (ω : Ωi * Ωj) (α : Type) (e : ix α) (x : α) =>
                         (gen_witness_update ci (fst ω) e x, gen_witness_update cj (snd ω) e x)
  ;  caller_obligation := fun (ω : Ωi * Ωj) (α : Type) (e : ix α) =>
                       gen_caller_obligation ci (fst ω) e /\ gen_caller_obligation cj (snd ω) e
  ;  callee_obligation := fun (ω : Ωi * Ωj) (α : Type) (e : ix α) (x : α) =>
                   gen_callee_obligation ci (fst ω) e x /\ gen_callee_obligation cj (snd ω) e x
  |}.

Infix "+" := cplus : contract_scope.

(** Finally, and as an example, we define a contract for the interface
    [STORE s] we discuss in [FreeSpec.Core.Impure].  As a reminder, the
    interface is defined as follows:

<<
Inductive STORE (s : Type) : interface :=
| Get : STORE s s
| Put (x : s) : STORE s unit.
>>

    For [STORE s], the best witness is the actual value of the mutable
    variable.  Therefore, the contract for [STORE s] may be [specs (STORE
    s) s], and the witness will be updated after each [Put] call. *)

Definition store_update (s : Type) :=
  fun (x : s) (α : Type) (e : STORE s α) (_ : α) =>
    match e with
    | Get => x
    | Put x' => x'
    end.

(** Assuming the mutable variable is being initialized prior to any impure
    computation interpretation, we do not have any obligations over the use of
    [STORE s] primitives.  We will get back to this assertion once we have
    defined our contract, but in the meantime, we define its callee obligation.

    The logic of these callee obligations is as follows: [Get] is expected to
    produce a result strictly equal to the witness, and we do not have any
    obligations about the result of [Put] (which belongs to [unit] anyway, so
    there is not much to tell). *)

Inductive o_callee_store (s : Type) (x : s) : forall (α : Type), STORE s α -> α -> Prop :=
| get_o_callee (x' : s) (equ : x = x') : o_callee_store s x s Get x'
| put_o_callee (x' : s) (u : unit) : o_callee_store s x unit (Put x') u.

(** The actual contract can therefore be defined as follows: *)

Definition store_specs (s : Type) : contract (STORE s) s :=
  {| witness_update := store_update s
  ;  caller_obligation := no_caller_obligation
  ;  callee_obligation := o_callee_store s
  |}.

(** Now, as we briefly mentionned, this contract allows for reasoning about an
    impure computation which uses the [STORE s] interface, assuming the mutable,
    global variable has been initialized.  We can define another contract that
    does not rely on such assumption, and on the contrary, requires an impure
    computation to initialize the variable prior to using it.

    In this context, the witness can solely be a boolean which tells if the
    variable has been initialized, and the [callee_obligation] will require the
    witness to be [true] to authorize a call of [Get].

    This is one of the key benefits of the FreeSpec approach: because the
    contracts are defined independently from impure computations and
    interfaces, we can actually define several contracts to consider
    different set of hypotheses. *)

(** * Reasoning with Contracts *)

(** ** Impure Computation Trustworthiness *)

(** An impure computation [p] is said respectful wrt. a contract [c] in
    accordance to a witness [ω] when it only uses primitives of [i] which
    satisfies [c] obligations. *)

Inductive respectful_impure `{MayProvide ix i} {α Ω} (c : contract i Ω) (ω : Ω) : impure ix α -> Prop :=

(** - Given a term [x], the computation [local x] is always respectful wrt. [c]
      in accordance to [ω], since it does not use any primitives. *)

| respectful_local (x : α)
  : respectful_impure c ω (local x)

(** - Given a primitive [e] and a continuation [f], if

      - [e] satisfies [c] caller obligation
      - [f] computations are respectful wrt. [c] in accordance to [ω'], where
        [ω'] is the witness updated after [e] interpretation

      then the impure computation [request_then e f] is respectful wrt. [c] in
      accordance to [ω]. *)

| respectful_request_some {β}
    (e : ix β) (f : β -> impure ix α)
    (req : gen_caller_obligation c ω e)
    (next : forall (x : β),
        gen_callee_obligation c ω e x
        -> respectful_impure c (gen_witness_update c ω e x) (f x))
  : respectful_impure c ω (request_then e f).

#[program]
Instance respectful_impure_Proper
  : Proper (equal ==> Basics.impl) (@respectful_impure ix i H α Ω c ω).

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
       now apply next.
Qed.

(** As is, the definition of [respectful_impure] would force FreeSpec users to
    unfold any impure computations they may combine together with [bind].  For
    instance, proving a computation of the form [bind p (λ _, p)] is respectful
    would require to prove [p] is respectful twice, for two different
    witnesses.  Moreover, it could be challenging to know, when interactively
    writing the proof script, when “the first [p]” stops, and when “the second
    [p]” starts.

    We need a way to compose proofs about impure computations the same way we
    compose impure computations with [bind].  We do that with the
    [respectful_run] predicate, which describes the potential outcomes of a
    computation in terms of results and witnesses. *)

Inductive respectful_run `{MayProvide ix i} {α Ω} (c : contract i Ω)
  : impure ix α -> Ω -> Ω -> α -> Prop :=

(** Given a term [x], and an initial witness [ω], a respectful run of
    [local x] produced a result [x] and a witness state [ω]. *)

| run_local (x : α) (ω : Ω)
  : respectful_run c (local x) ω ω x

(** Given an initial witness [ω], a primitive [e] which satisfies [c]
    caller obligations, and a continuation [f], a result [x] for [e] which
    satisfies [c] callee obligations, if we can show that there is a respectful
    run of [f x] which produces a term [y] and a witness [ω'], then there is a
    respectful run of [request_then e f] which produces a result [y] and a
    witness [ω']. *)

| run_request {β} (ω : Ω)
    (e : ix β) (o_caller : gen_caller_obligation c ω e) (f : β -> impure ix α)
    (x : β) (o_callee : gen_callee_obligation c ω e x)
    (ω' : Ω) (y : α) (rec : respectful_run c (f x) (gen_witness_update c ω e x) ω' y)
  : respectful_run c (request_then e f) ω ω' y.

(** Given a contract [c] and a witness [ω] an impure computation [p] and a
    continuation [f] if

    - [p] is a respectful impure computation wrt. [c] in accordance to [ω], and
    - for all result [x] and witness [ω'] produces by [p], [f x] is respectful,

    then [bind p f] is respectful. *)

Lemma respectful_bind_respectful_run `{MayProvide ix i} {α β Ω}
  (c : contract i Ω) (ω : Ω)
  (p : impure ix α) (f : α -> impure ix β)
  (respect : respectful_impure c ω p)
  (run : forall (x : α) (ω' : Ω),
      respectful_run c p ω ω' x -> respectful_impure c ω' (f x))
  : respectful_impure c ω (impure_bind p f).

Proof.
  revert ω respect run.
  induction p; intros ω respect run.
  + apply run.
    constructor.
  + cbn.
    inversion respect; ssubst.
    constructor.
    ++ apply req.
    ++ intros y o_callee_x.
       apply H0; [ auto | ].
       intros z ω' run'.
       apply run.
       econstructor; eauto.
Qed.

Hint Resolve respectful_bind_respectful_run : freespec.

Lemma respectful_bind_exists_respectful_run `{MayProvide ix i} {α β Ω}
    (c : contract i Ω) (ω ω' : Ω)
    (p : impure ix α) (f : α -> impure ix β) (x : β)
    (respect : respectful_run c (impure_bind p f) ω ω' x)
  : exists (ω'' : Ω) (y : α),
    respectful_run c p ω ω'' y /\ respectful_run c (f y) ω'' ω' x.

Proof.
  revert respect.
  revert ω ω'.
  induction p; intros ω ω' respect.
  + exists ω; exists x0.
    split.
    ++ constructor.
    ++ exact respect.
  + inversion respect; ssubst.
    apply H0 in rec.
    destruct rec as [ω'' [y [trust1 trust2]]].
    exists ω''; exists y.
    split; auto.
    constructor 2 with (x := x0); auto.
Qed.

#[program]
Instance respectful_run_Proper
  : Proper (equal ==> eq ==> eq ==> eq ==> Basics.impl) (@respectful_run ix i H α Ω c).

Next Obligation.
  add_morphism_tactic.
  unfold Basics.impl.
  intros p q equ.
  induction equ.
  + intros ω ω' y run.
    now inversion run; subst.
  + intros ω ω' y run.
    inversion run; ssubst.
    constructor 2 with (x := x).
    ++ auto.
    ++ auto.
    ++ now apply H0.
Qed.

(** ** Semantics Compliance *)

(** Given a semantics [sem], and a witness [ω] if [sem] computes results which
    satisfies [c] callee obligations for effects which satisfy [c] caller
    obligations and if the resulting semantics produces after interpreting [e]
    complies to [c] in accordance to [ω'], where [ω'] is the new witness state
    after [e] interpretation then [sem] complies to [c] in accordance to [ω] *)

CoInductive compliant_semantics `{MayProvide ix i} {Ω} (c : contract i Ω) : Ω -> semantics ix -> Prop :=
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
  + intros a [ | st' ] _.
    ++ now constructor.
    ++ now constructor.
  + intros a e req.
    cbn.
    assert (R : exec_effect (store st) e = store (store_update s st a e (eval_effect (store st) e)))
      by now destruct e as [ | st' ].
    rewrite R.
    apply compliant_semantics_rec.
Qed.

Lemma compliant_semantics_caller_obligation_callee_obligation `{MayProvide ix i} {Ω α} (c : contract i Ω) (ω : Ω)
  (e : ix α) (o_caller : gen_caller_obligation c ω e)
  (sem : semantics ix) (comp : compliant_semantics c ω sem)
  : gen_callee_obligation c ω e (eval_effect sem e).

Proof.
  inversion comp; ssubst.
  now apply o_callee.
Qed.

Hint Resolve compliant_semantics_caller_obligation_callee_obligation : freespec.

Lemma compliant_semantics_caller_obligation_compliant `{MayProvide ix i} {Ω α} (c : contract i Ω) (ω : Ω)
  (e : ix α) (o_caller : gen_caller_obligation c ω e)
  (sem : semantics ix) (comp : compliant_semantics c ω sem)
  : compliant_semantics c (gen_witness_update c ω e (eval_effect sem e)) (exec_effect sem e).

Proof.
  inversion comp; ssubst.
  now apply next.
Qed.

Hint Resolve compliant_semantics_caller_obligation_compliant : freespec.

Lemma compliant_semantics_exec_effect_equ `{MayProvide ix i} {Ω α} (c : contract i Ω) (ω : Ω)
  (sem sem' : semantics ix) (equ : sem === sem')
  (e : ix α)
  : exec_effect sem e === exec_effect sem' e.

Proof.
  inversion equ; ssubst.
  specialize step_equiv with α e.
  now inversion step_equiv; ssubst.
Qed.

Hint Resolve compliant_semantics_exec_effect_equ : freespec.

#[program]
Instance compliant_semantics_Proper : Proper (equal ==> Basics.impl) (@compliant_semantics ix i H Ω c ω).

Next Obligation.
  add_morphism_tactic.
  revert ω.
  cofix compliant_semantics_Proper; intros ω.
  intros σ σ' equ comp.
  destruct comp.
  constructor.
  + now setoid_rewrite <- equ.
  + intros a e o_caller.
    apply (compliant_semantics_Proper (gen_witness_update c ω e (eval_effect σ' e)) (exec_effect sem e)).
    ++ auto with freespec.
    ++ rewrite <- equ at 1.
       now apply next.
Qed.

Lemma no_contract_compliant_semantics `{MayProvide ix i} (sem : semantics ix) (u : unit)
  : compliant_semantics (no_contract i) u sem.

Proof.
  revert sem.
  cofix no_contract_compliant_semantics; intros sem.
  constructor.
  + trivial.
  + intros α e req.
    unfold gen_witness_update.
    destruct (proj_p e); [ apply no_contract_compliant_semantics | auto ].
Qed.

Hint Resolve no_contract_compliant_semantics : freespec.

#[local]
Fixpoint witness_impure_aux `{MayProvide ix i} {Ω α}
  (sem : semantics ix) (p : impure ix α) (c : contract i Ω) (ω : Ω) : interp_out ix α * Ω :=
  match p with
  | local x => (mk_out x sem, ω)
  | request_then e f =>
    let out := run_effect sem e in
    let res := interp_result out in
    witness_impure_aux (interp_next out) (f res) c (gen_witness_update c ω e res)
  end.

#[program]
Instance witness_impure_aux_Proper_2
  : Proper (eq ==> equal ==> eq ==> eq ==> eq) (@witness_impure_aux ix i H Ω a).

Next Obligation.
  add_morphism_tactic.
  intros sem p q equp c ω.
  revert sem ω.
  induction equp; intros sem ω.
  + reflexivity.
  + cbn.
    apply H0.
Qed.

Lemma fst_witness_impure_aux_run_impure `{MayProvide ix i} {Ω α}
  (sem : semantics ix) (p : impure ix α) (c : contract i Ω) (ω : Ω)
  : fst (witness_impure_aux sem p c ω) = run_impure sem p.

Proof.
  revert sem ω.
  induction p; intros sem ω.
  + reflexivity.
  + apply H0.
Qed.

Hint Rewrite @fst_witness_impure_aux_run_impure : freespec.

Definition witness_impure `{MayProvide ix i} {Ω α}
  (sem : semantics ix) (p : impure ix α) (c : contract i Ω) (ω : Ω) : Ω :=
  snd (witness_impure_aux sem p c ω).

#[program]
Instance witness_impure_Proper
  : Proper (eq ==> equal ==> eq ==> eq ==> eq) (@witness_impure ix i H Ω α).

Next Obligation.
  add_morphism_tactic.
  unfold witness_impure.
  intros sem p q equp c ω.
  now rewrite equp.
Qed.

Lemma compliant_semantics_respectful_impure_gives_respectful_run `{MayProvide ix i} {Ω α}
  (c : contract i Ω) (ω : Ω) (p : impure ix α) (trust : respectful_impure c ω p)
  (sem : semantics ix) (comp : compliant_semantics c ω sem)
  : respectful_run c p ω (witness_impure sem p c ω) (eval_impure sem p).

Proof.
  revert sem comp trust. revert ω.
  induction p; intros ω sem comp trust.
  + constructor.
  + inversion trust; ssubst.
    inversion comp; ssubst.
    econstructor; auto.
    apply H0.
    ++ now apply next0.
    ++ inversion trust; ssubst.
       apply next1.
       now apply o_callee.
Qed.

Hint Resolve compliant_semantics_respectful_impure_gives_respectful_run : freespec.

Lemma witness_impure_request_then_equ `{MayProvide ix i} {Ω α β} (c : contract i Ω) (ω : Ω)
  (sem : semantics ix) (e : ix α) (f : α -> impure ix β)
  : witness_impure sem (request_then e f) c ω
    = witness_impure (exec_effect sem e)
                     (f (eval_effect sem e))
                     c
                     (gen_witness_update c ω e (eval_effect sem e)).

Proof eq_refl.

Hint Rewrite @witness_impure_request_then_equ : freespec.

Lemma respectful_impure_compliant_specs `{MayProvide ix i} {Ω α} (c : contract i Ω) (ω : Ω)
  (p : impure ix α) (trust : respectful_impure c ω p)
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

Hint Resolve respectful_impure_compliant_specs : freespec.

Lemma gen_callee_obligation_equ {α Ωi Ωj} `{Provide ix i} `{Provide ix j}
    (ci : contract i Ωi) (ωi : Ωi)
    (cj : contract j Ωj) (ωj : Ωj)
    (e : ix α) (x : α)
  : gen_callee_obligation ci ωi e x /\ gen_callee_obligation cj ωj e x
    <-> gen_callee_obligation (ci + cj) (ωi, ωj) e x.

Proof.
  split; auto.
Qed.

Lemma gen_caller_obligation_equ {α Ωi Ωj} `{Provide ix i} `{Provide ix j}
    (ci : contract i Ωi) (ωi : Ωi) (cj : contract j Ωj) (ωj : Ωj) (e : ix α)
  : gen_caller_obligation ci ωi e /\ gen_caller_obligation cj ωj e
    <-> gen_caller_obligation (ci + cj) (ωi, ωj) e.

Proof.
  split; auto.
Qed.

Lemma respectful_impure_generalize `{Provide ix i} `{Provide ix j} {α Ωi Ωj}
    (p : impure ix α)
    (ci : contract i Ωi) (ωi : Ωi) (cj : contract j Ωj) (ωj : Ωj)
  : respectful_impure ci ωi p
    -> respectful_impure cj ωj p
    -> respectful_impure (ci + cj) (ωi, ωj) p.

Proof.
  revert ωi ωj.
  induction p; intros ωi ωj.
  + intros.
    constructor.
  + intros trust trust'.
    inversion trust; ssubst.
    inversion trust'; ssubst.
    constructor.
    ++ rewrite <- gen_caller_obligation_equ.
       now split.
    ++ intros x o_callee.
       rewrite <- gen_callee_obligation_equ in o_callee.
       apply H3; [ apply next | apply next0 ]; apply o_callee.
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

Definition correct_component {i jx Ωi Ωj}
  (c : component i jx) `{MayProvide jx j}
  (ci : contract i Ωi) (cj : contract j Ωj)
  (pred : Ωi -> Ωj -> Prop) : Prop :=
  forall (ωi : Ωi) (ωj : Ωj) (init : pred ωi ωj)
    (α : Type) (e : i α) (o_caller : caller_obligation ci ωi e),
    respectful_impure cj ωj (c α e) /\
    forall (x : α) (ωj' : Ωj)
      (run : respectful_run cj (c α e) ωj ωj' x),
      callee_obligation ci ωi e x /\ pred (witness_update ci ωi e x) ωj'.

(** Once we have proven [c] is correct wrt. to [speci] and [specj] with [pred]
    acting as an invariant throughout [c] life, we show we can derive a
    semantics from [c] with an initial state [st] which complies to [speci] in
    accordance to [ωi] if we use a semantics of [j] which complies to [specj] in
    accordance to [ωj], where [pred ωi st ωj] is satisfied. *)

Lemma respectful_impure_compliant_specs_respectful_run `{MayProvide ix i} {a Ω}
    (spec : contract i Ω) (ω : Ω)
    (sem : semantics ix) (comp : compliant_semantics spec ω sem)
    (p : impure ix a) (trust : respectful_impure spec ω p)
  : respectful_run spec p ω (witness_impure sem p spec ω) (eval_impure sem p).

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
  (c : component i jx) (ci : contract i Ωi) (cj : contract j Ωj)
  (pred : Ωi -> Ωj -> Prop)
  (correct : correct_component c ci cj pred)
  (ωi : Ωi) (ωj : Ωj) (inv : pred ωi ωj)
  (sem : semantics jx) (comp : compliant_semantics cj ωj sem)
  : compliant_semantics ci ωi (derive_semantics c sem).

Proof.
  revert ωi ωj inv sem comp.
  cofix correct_component_derives_compliant_semantics.
  intros ωi ωj inv sem comp.
  unfold correct_component in correct.
  specialize (correct ωi ωj inv).
  constructor; intros a e req; specialize (correct a e req);
    destruct correct as [trust run].
    specialize run with (eval_impure sem (c a e))
                        (witness_impure (H := H) sem (c a e) cj ωj).
  + apply run.
    auto with freespec.
  + eapply correct_component_derives_compliant_semantics.
    ++ apply run.
       apply respectful_impure_compliant_specs_respectful_run; auto.
    ++ fold (exec_impure sem (c a e)).
       auto with freespec.
Qed.

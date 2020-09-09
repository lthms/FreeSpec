(* FreeSpec
 * Copyright (C) 2018–2020 ANSSI
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

(** In FreeSpec, there is no particular semantics attach to interface's
    primitives. Once an interface has been defined, we can provide one (or
    more) operational semantics to interpret its primitives. *)

(** * Definition *)

(** An operational [semantics] for the interface [i] is coinductively defined as
    a function which can be used to interpret any primitive of [i]; it produces
    an [interp_out] term. *)

From Coq Require Import Program Setoid Morphisms.
From ExtLib Require Import Monad StateMonad.
From FreeSpec.Core Require Export Interface ImpureFacts.

#[local] Open Scope signature_scope.

CoInductive semantics (i : interface) : Type :=
| mk_semantics (f : forall (α : Type), i α -> α * semantics i) : semantics i.

Arguments mk_semantics [i] (f).

(** Thus, a [semantics] does not only compute a result for a primitive, but also
    provides a new semantics.  This is necessary to model impurity: the same
    primitive may or may not return the same result when called several
    times.

    As for interfaces, the simpler [semantics] is the operational semantics for
    [iempty], the empty interface. *)

Definition iempty_semantics : semantics iempty :=
  mk_semantics (fun α (e : iempty α) => match e with end).

(** We also provide a semantics for the [STORE s] interface: *)

CoFixpoint store {s} (init : s) : semantics (STORE s) :=
  mk_semantics (fun α (e : STORE s α) =>
                  match e with
                  | Get => (init, store init)
                  | Put next => (tt, store next)
                  end).

(** We provide several helper functions to interpret primitives with
    semantics. *)

Definition run_effect {i α} (sem : semantics i) (e : i α) : α * semantics i :=
  match sem with mk_semantics f => f α e end.

Definition eval_effect {i α} (sem : semantics i) (e : i α) : α :=
  fst (run_effect sem e).

Definition exec_effect {i α} (sem : semantics i) (e : i α) : semantics i :=
  snd (run_effect sem e).

Lemma run_effect_equation {i α} (sem : semantics i) (e : i α)
  : run_effect sem e = (eval_effect sem e, exec_effect sem e).

Proof.
  unfold eval_effect, exec_effect.
  destruct run_effect; reflexivity.
Qed.

Definition interface_to_state {i} : i ~> state (semantics i) :=
  fun a e => mkState (fun sem => run_effect sem e).

(** Besides, and similarly to interfaces, operational semantics can and should
    be composed together.  To that end, we provide the [semplus] operator. *)

CoFixpoint semplus {i j} (sem_i : semantics i) (sem_j : semantics j)
  : semantics (i + j) :=
  mk_semantics (fun _ e =>
                  match e with
                  | in_left e =>
                    let (x, out) := run_effect sem_i e in
                    (x, semplus out sem_j)
                  | in_right e =>
                    let (x, out) := run_effect sem_j e in
                    (x, semplus sem_i out)
                  end).

Declare Scope semantics_scope.
Bind Scope semantics_scope with semantics.
Delimit Scope semantics_scope with semantics.

Infix "*" := semplus : semantics_scope.

(** * Equivalence *)

(** We say two semantics are equivalent when they produce equivalent outputs
    given the same primitive. *)

CoInductive semantics_eq {i} : semantics i -> semantics i -> Prop :=
| semantics_eq_rec
    (sem sem' : semantics i)
    (res_eq : forall {a} (e : i a), eval_effect sem e = eval_effect sem' e)
    (next_eqv : forall {a} (e : i a),
        semantics_eq (exec_effect sem e) (exec_effect sem' e))
  : semantics_eq sem sem'.

Infix "===" := semantics_eq : semantics_scope.

(** We prove [semantics_eq] is an equivalence, that is the relation is (1)
    reflexive, (2) symmetric, and (3) transitive. *)

#[program]
Instance semantics_Equivalence (i : interface) : Equivalence (@semantics_eq i).

Next Obligation.
  cofix semantics_eqv_refl.
  intros sem.
  constructor; intros α e.
  + reflexivity.
  + apply semantics_eqv_refl.
Qed.

Next Obligation.
  cofix semantics_eqv_sym.
  intros sem sem' equiv.
  destruct equiv as [sem sem' step].
  constructor; intros α e.
  + now symmetry.
  + now apply semantics_eqv_sym.
Qed.

Next Obligation.
  cofix semantics_eqv_trans.
  intros sem sem' sem'' equiv equiv'.
  destruct equiv as [sem sem' equ].
  destruct equiv' as [sem' sem'' equ'].
  constructor; intros α e;
    specialize equ with α e;
    specialize equ' with α e;
    inversion equ; ssubst;
      inversion equ'; ssubst.
  + now transitivity (eval_effect sem' e).
  + eapply semantics_eqv_trans; [ apply next_eqv | apply next_eqv0 ].
Qed.

Definition run_effect_eq `(x : α * semantics i) (y : α * semantics i) : Prop :=
  fst x = fst y /\ (snd x === snd y)%semantics.

#[program]
Instance run_effect_Equivalence : @Equivalence (a * semantics i) run_effect_eq.

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

#[program]
Instance fst_Proper : Proper (run_effect_eq ==> eq) (@fst α (semantics i)).

Next Obligation.
  add_morphism_tactic.
  intros [x next] [y next'] [equ1 equ2].
  apply equ1.
Qed.

#[program]
Instance snd_Proper : Proper (run_effect_eq ==> semantics_eq) (@snd α (semantics i)).

Next Obligation.
  add_morphism_tactic.
  intros [x next] [y next'] [equ1 equ2].
  apply equ2.
Qed.

#[program]
Instance prod_Proper : Proper (eq ==> semantics_eq ==> run_effect_eq) (@pair a (semantics i)).

Next Obligation.
  add_morphism_tactic.
  intros x sem sem' equ.
  split.
  + reflexivity.
  + apply equ.
Qed.

Instance run_effect_Proper
  : Proper (semantics_eq ==> eq ==> run_effect_eq) (@run_effect i α).

Proof.
  add_morphism_tactic.
  intros sem sem' equ e.
  rewrite run_effect_equation.
  inversion equ; subst.
  split.
  + apply res_eq.
  + apply next_eqv.
Qed.

#[program]
Instance eval_effect_Proper : Proper (semantics_eq ==> eq ==> eq) (@eval_effect i α).

Next Obligation.
  add_morphism_tactic.
  intros o o' equ e.
  unfold eval_effect.
  now rewrite equ.
Qed.

#[program]
Instance exec_effect_Proper : Proper (semantics_eq ==> eq ==> semantics_eq) (@exec_effect i α).

Next Obligation.
  add_morphism_tactic.
  intros o o' equ e.
  unfold exec_effect.
  now rewrite equ.
Qed.

Lemma eval_semplus_in_left_eq `(semi : semantics i) `(semj : semantics j) `(e : i α)
  : eval_effect (semi * semj) (in_left e) = eval_effect semi e.

Proof.
  unfold eval_effect; cbn.
  destruct semi as [semi].
  cbn.
  now destruct (semi α e).
Qed.

Lemma eval_semplus_in_right_eq `(semi : semantics i) `(semj : semantics j) `(e : j α)
  : eval_effect (semi * semj) (in_right e) = eval_effect semj e.

Proof.
  unfold eval_effect; cbn.
  destruct semj as [semj].
  cbn.
  now destruct (semj α e).
Qed.

Lemma exec_semplus_in_left_eqv `(semi : semantics i) `(semj : semantics j) `(e : i α)
  : exec_effect (semi * semj) (in_left e) = (semplus (exec_effect semi e) semj).

Proof.
  unfold exec_effect; cbn.
  destruct semi as [semi].
  cbn.
  now destruct (semi _ e).
Qed.

Lemma exec_semplus_in_right_eqv `(semi : semantics i) `(semj : semantics j) `(e : j α)
  : exec_effect (semi * semj) (in_right e) = (semplus semi (exec_effect semj e)).

Proof.
  unfold exec_effect; cbn.
  destruct semj as [semj].
  cbn.
  now destruct (semj _ e).
Qed.

#[program]
Instance semplus_Proper i j
  : Proper (semantics_eq ==> semantics_eq ==> semantics_eq) (@semplus i j).

Next Obligation.
  add_morphism_tactic.
  cofix semplus_Proper.
  intros semi semi' equi semj semj' equj.
  constructor; intros α e; destruct e.
  + repeat rewrite eval_semplus_in_left_eq.
    now inversion equi.
  + repeat rewrite eval_semplus_in_right_eq.
    now inversion equj.
  + repeat rewrite exec_semplus_in_left_eqv.
    apply semplus_Proper; auto.
    inversion equi.
    apply next_eqv.
  + repeat rewrite exec_semplus_in_right_eqv.
    apply semplus_Proper; auto.
    inversion equj.
    apply next_eqv.
Qed.

(** * Interpreting Impure Computations *)

(** A term of type [impure a] describes an impure computation expected to return
    a term of type [a].  Interpreting this term means actually realizing the
    computation and producing the result.  This requires to provide an
    operational semantics for the interfaces used by the computation.

    Some operational semantics may be defined in Gallina by means of the
    [semantics] type. In such a case, we provide helper functions to use them in
    conjunction with [impure] terms. The terminology follows a logic similar to
    the Haskell state monad:

    - [run_impure] interprets an impure computation [p] with an operational
      semantics [sem], and returns both the result of [p] and the new
      operational semantics to use afterwards.
    - [eval_impure] only returns the result of [p].
    - [exec_impure] only returns the new operational semantics. *)

Definition to_state {i} : impure i ~> state (semantics i) :=
  impure_lift interface_to_state.

Arguments to_state {i α} _.

Definition run_impure {i a} (sem : semantics i) (p : impure i a) : a * semantics i :=
  runState (to_state p) sem.

Definition eval_impure {i a} (sem : semantics i) (p : impure i a) : a :=
  fst (run_impure sem p).

Definition exec_impure {i a} (sem : semantics i) (p : impure i a) : semantics i :=
  snd (run_impure sem p).

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
    specialize next_eqv with _ e.
    apply H in next_eqv.
    rewrite <- res_eq.
    exact next_eqv.
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

#[local]
Fixpoint with_semantics {ix j α} (sem : semantics j) (p : impure (ix + j) α)
  : impure ix α :=
  match p with
  | local x => local x
  | request_then (in_right e) f =>
    let (res, next) := run_effect sem e in
    with_semantics next (f res)
  | request_then (in_left e) f =>
    request_then e (fun x => with_semantics sem (f x))
  end.

(** We provide [with_store], a helper function to locally provide a mutable
    variable. *)

Definition with_store {ix s a} (x : s) (p : impure (ix + STORE s) a)
  : impure ix a :=
  with_semantics (store x) p.

(** Nesting [with_semantics] calls works to some extends. If each
    [with_semantics] provides a different interface from the rest of the stack,
    then everything behaves as expected. If, for some reason, you end up in a
    situation where you provide the exact same interface twice (typically if you
    use [with_store]), then the typeclass inferences will favor the deepest one
    in the stack. For instance,

<<
Compute (with_store 0 (with_store 1 get)).
>>

    returns

<<
     = local 1
     : impure ?ix nat
>> *)

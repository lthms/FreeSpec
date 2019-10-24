(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2018–2019 Thomas Letan <thomas.letan@ssi.gouv.fr>
 *
 * This impure is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This impure is distributed in the hope that it will be useful,
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

(** ** Definition *)

(** An operational [semantics] for the interface [i] is coinductively defined as
    a function which can be used to interpret any primitive of [i]; it produces
    an [interp_out] terms. *)

From Coq Require Import Program Setoid Morphisms.
From Prelude Require Import All.
From FreeSpec.Core Require Import Interface Impure.

#[local] Open Scope signature_scope.

CoInductive semantics (i : interface) : Type :=
| mk_semantics (f : forall (α : Type), i α -> interp_out i α) : semantics i

(** A term of type [interp_out i a] is therefore the result of the
    interpretation of a given primitive [i a]. It provides a result for this
    primitive (of type [a]), and the new semantics to use to interpret the next
    primitive of [i]. *)

with interp_out (i : interface) : Type -> Type :=
| mk_out {α} (x : α) (sem : semantics i) : interp_out i α.

Arguments mk_semantics [i] (f).
Arguments mk_out [i α] (x sem).

(** Thus, a [semantics] does not only compute a result for a primitive, but also
    provides a new semantics.  This is necessary to model impurity: the same
    primitive may or may not return the same result when called several
    times. *)

(** As for interfaces, the simpler [semantics] is the operational semantics for
    [iempty], the empty interface. *)

Definition iempty_semantics : semantics iempty :=
  mk_semantics (fun α (e : iempty α) => match e with end).

(** We also provide a semantics for the [STORE s] interface: *)

CoFixpoint store {s} (init : s) : semantics (STORE s) :=
  mk_semantics (fun α (e : STORE s α) =>
                  match e with
                  | Get => mk_out init (store init)
                  | Put next => mk_out tt (store next)
                  end).

(** We provide several helper functions to interpret primitives with
    semantics. *)

Definition run_effect {i α} (sem : semantics i) (e : i α) : interp_out i α :=
  match sem with mk_semantics f => f _ e end.

Definition interp_result {i α} (step : interp_out i α) : α :=
  match step with mk_out x _ => x end.

Definition interp_next {i α} (step : interp_out i α) : semantics i :=
  match step with mk_out _ sem => sem end.

Definition eval_effect {i α} (sem : semantics i) (e : i α) : α :=
  interp_result (run_effect sem e).

Definition exec_effect {i α} (sem : semantics i) (e : i α) : semantics i :=
  interp_next (run_effect sem e).

(** Besides, and similarly to interfaces, operational semantics can and should
    be composed together.  To that end, we provide the [semplus] operator. *)

CoFixpoint semplus {i j} (sem_i : semantics i) (sem_j : semantics j)
  : semantics (i + j) :=
  mk_semantics (fun _ e =>
                  match e with
                  | in_left e =>
                    let out := run_effect sem_i e in
                    mk_out (interp_result out) (semplus (interp_next out) sem_j)
                  | in_right e =>
                    let out := run_effect sem_j e in
                    mk_out (interp_result out) (semplus sem_i (interp_next out))
                  end).

Declare Scope semantics_scope.
Bind Scope semantics_scope with semantics.

Infix "*" := semplus : semantics_scope.

(** ** Equivalence *)

(** We say two semantics are equivalent when they produce equivalent outputs
    given the same primitive. *)

CoInductive semantics_equiv {i} : semantics i -> semantics i -> Prop :=
| semantics_equiv_rec
    (sem sem' : semantics i)
    (step_equiv : forall {a} (e : i a),
        interp_out_equiv (run_effect sem e) (run_effect sem' e))
  : semantics_equiv sem sem'

(** Two interpretation output are said equivalent when they carry the same
    result, and they provide equivalent semantics to use afterwards. *)

with interp_out_equiv {i} : forall {a : Type}, interp_out i a -> interp_out i a -> Prop :=
| step_equiv {a}
    (o o' : interp_out i a)
    (res_eq : interp_result o = interp_result o')
    (next_equiv : semantics_equiv (interp_next o) (interp_next o'))
  : interp_out_equiv o o'.

(** We prove [semantics_equiv] is an equivalence, that is the relation is (1)
    reflexive, (2) symmetric, and (3) transitive. *)

#[program]
Instance semantics_equiv_Equivalence (i : interface) : Equivalence (@semantics_equiv i).

Obligation 1.
  cofix semantics_equiv_refl.
  intros sem.
  constructor.
  intros a e.
  constructor; [ reflexivity |].
  apply semantics_equiv_refl.
Qed.

Obligation 2.
  cofix semantics_equiv_sym.
  intros sem sem' equiv.
  destruct equiv as [sem sem' step].
  constructor.
  intros a e.
  specialize step with a e.
  destruct step.
  constructor.
  + now symmetry.
  + now apply semantics_equiv_sym.
Qed.

Obligation 3.
  cofix semantics_equiv_trans.
  intros sem sem' sem'' equiv equiv'.
  destruct equiv as [sem sem' equ].
  destruct equiv' as [sem' sem'' equ'].
  constructor; intros a e.
  specialize equ with a e.
  specialize equ' with a e.
  inversion equ; ssubst.
  inversion equ'; ssubst.
  constructor.
  + now transitivity (eval_effect sem' e).
  + eapply semantics_equiv_trans; [ apply next_equiv | apply next_equiv0 ].
Qed.

(** We use [semantics_equiv] as the [Equality] relation for [semantics]. *)

#[program]
Instance semantics_Equality (i : interface) : Equality (semantics i).

#[global]
Opaque semantics_Equality.

(** We proceed similarly with [interp_out_equiv]: we first prove it is an
    equivalence, then we use this relation as the [Equality] relation for
    [interp_out]. *)

#[program]
Instance interp_out_Equivalence : Equivalence (@interp_out_equiv i α).

Obligation 1.
  intros [x sem].
  constructor; reflexivity.
Qed.

Obligation 2.
  intros o o' equ.
  inversion equ; ssubst.
  now constructor.
Qed.

Obligation 3.
  intros o o' o'' equ equ'.
  inversion equ; ssubst.
  inversion equ'; ssubst.
  constructor.
  + now transitivity (interp_result o').
  + now transitivity (interp_next o').
Qed.

#[program]
Instance interp_out_Equality (i : interface) (α : Type) : Equality (interp_out i α).

#[global]
Opaque interp_out_Equality.

(** Since [interp_out_equiv] and [semantics_equiv] are two equivalence, we can
    use them with the [rewrite] tactics, as long as we provide valid [Proper]
    instances.  We proceed accordingly in FreeSpec.Core, as systematically as
    possible. *)

#[program]
Instance mk_out_Proper : Proper (eq ==> 'equal ==> 'equal) (@mk_out i α).

Next Obligation.
  add_morphism_tactic.
  intros x sem sem' equ.
  constructor.
  + reflexivity.
  + apply equ.
Qed.

#[program]
Instance run_effect_Proper : Proper ('equal ==> eq ==> 'equal) (@run_effect i α).

Next Obligation.
  add_morphism_tactic.
  intros sem sem' equ p.
  inversion equ; ssubst.
  apply step_equiv0.
Qed.

#[program]
Instance interp_result_Proper : Proper ('equal ==> eq) (@interp_result i α).

Next Obligation.
  add_morphism_tactic.
  intros o o' equ.
  now inversion equ; ssubst.
Qed.

#[program]
Instance interp_next_Proper : Proper ('equal ==> 'equal) (@interp_next i α).

Next Obligation.
  add_morphism_tactic.
  intros o o' equ.
  now inversion equ; ssubst.
Qed.

#[program]
Instance eval_effect_Proper : Proper ('equal ==> eq ==> eq) (@eval_effect i α).

Next Obligation.
  add_morphism_tactic.
  intros o o' equ e.
  unfold eval_effect.
  now rewrite equ.
Qed.

#[program]
Instance exec_effect_Proper : Proper ('equal ==> eq ==> 'equal) (@exec_effect i α).

Next Obligation.
  add_morphism_tactic.
  intros o o' equ e.
  unfold exec_effect.
  now rewrite equ.
Qed.

Lemma semantics_equiv_interp_next_effect {i α}
  (sem sem' : semantics i) (equ : sem == sem') (e : i α)
  : interp_next (run_effect sem e) == interp_next (run_effect sem' e).

Proof.
  inversion equ; ssubst.
  specialize step_equiv0 with α e.
  inversion step_equiv0; ssubst.
  apply next_equiv.
Qed.

Hint Resolve semantics_equiv_interp_next_effect : freespec.

Lemma semantics_equiv_exec_effect {i α}
  (sem sem' : semantics i) (equ : sem == sem') (e : i α)
  : exec_effect sem e == exec_effect sem' e.

Proof.
  unfold exec_effect.
  auto with freespec.
Qed.

Hint Resolve semantics_equiv_exec_effect : freespec.

#[program]
Instance semplus_Proper : Proper ('equal ==> 'equal ==> 'equal) (@semplus i j).

Next Obligation.
  add_morphism_tactic.
  cofix semplus_Proper.
  intros semi semi' equi semj semj' equj.
  constructor.
  intros a e.
  destruct e; constructor; cbn.
  + now rewrite equi.
  + apply semplus_Proper; auto with freespec.
  + now rewrite equj.
  + apply semplus_Proper; auto with freespec.
Qed.

(** ** Interpreting Impure Computations *)

(** A term of type [impure a] describes an impure computation expected to return
    a term of type [a].  Interpreting this term means actually realizing the
    computation and producing the result.  This requires to provide an
    operational semantics for the interfaces used by the computation.

    Some operational semantics may be defined in Gallina by means of the
    [semantics] type. In such a case, we provide helpers functions to use them
    in conjunction with [impure] terms. The terminology follows a similar logic than the
    Haskell state monad:

    - [run_impure] interprets an impure computation [p] with an operational
      semantics [sem], and returns both the result of [p] and the new
      operational semantics to use afterwards.
    - [eval_impure] only returns the result of [p].
    - [exec_impure] only returns the new operational semantics. *)

Fixpoint run_impure {i a} (sem : semantics i) (p : impure i a) : interp_out i a :=
  match p with
  | local x =>
    mk_out x sem
  | request_then e f =>
    let s := run_effect sem e in
    run_impure (interp_next s) (f (interp_result s))
  end.

Definition eval_impure {i a} (sem : semantics i) (p : impure i a) : a :=
  interp_result (run_impure sem p).

Definition exec_impure {i a} (sem : semantics i) (p : impure i a) : semantics i :=
  interp_next (run_impure sem p).

(** We provide several lemmas and the necessary [Proper] instances to use these
    functions in conjunction with [semantics_equiv] and [impure_equiv]. *)

Lemma run_impure_request_then_equ {i a b} (sem : semantics i)
  (e : i a) (f : a -> impure i b)
  : run_impure sem (request_then e f) = run_impure (exec_effect sem e) (f (eval_effect sem e)).
Proof eq_refl.

Hint Rewrite @run_impure_request_then_equ : freespec.

Lemma semantics_equiv_interp_next_impure {i a}
  (sem sem' : semantics i) (equ : sem == sem') (p : impure i a)
  : interp_next (run_impure sem p) == interp_next (run_impure sem' p).
Proof.
  revert sem sem' equ.
  induction p; intros sem sem' equ.
  + apply equ.
  + cbn.
    unfold exec_impure.
    cbn.
    rewrite equ at 2.
    apply H.
    auto with freespec.
Qed.

Hint Resolve semantics_equiv_interp_next_impure : freespec.

Lemma semantics_equiv_exec_impure {i a}
  (sem sem' : semantics i) (equ : sem == sem') (p : impure i a)
  : exec_impure sem p == exec_impure sem' p.
Proof.
  unfold exec_impure.
  auto with freespec.
Qed.

Hint Resolve semantics_equiv_exec_impure : freespec.

#[program]
Instance run_impure_Proper_1 (i : interface) (a : Type)
  : Proper ('equal ==> eq ==> 'equal) (@run_impure i a).

Next Obligation.
  add_morphism_tactic.
  intros sem sem' equ p.
  revert sem sem' equ.
  induction p; intros sem sem' equ.
  + cbn.
    now rewrite equ.
  + cbn.
    rewrite equ at 2.
    auto with freespec.
Qed.

#[program]
Instance run_impure_Proper_2 (i : interface) (a : Type)
  : Proper (eq ==> 'equal ==> 'equal) (@run_impure i a).

Next Obligation.
  add_morphism_tactic.
  intros sem p q equ.
  revert sem.
  induction equ; intros sem.
  + reflexivity.
  + apply H.
Qed.

#[program]
Instance eval_impure_Proper (i : interface) (a : Type)
  : Proper ('equal ==> 'equal ==> eq) (@eval_impure i a).

Next Obligation.
  add_morphism_tactic.
  intros sem sem' equ1 p q equ2.
  unfold eval_impure.
  now rewrite equ1, equ2.
Qed.

#[program]
Instance exec_impure_Proper (i : interface) (a : Type)
  : Proper ('equal ==> 'equal ==> 'equal) (@exec_impure i a).

Next Obligation.
  add_morphism_tactic.
  intros sem sem' equ1 p q equ2.
  unfold exec_impure.
  now rewrite equ1, equ2.
Qed.

Lemma run_impure_equiv {i a} (p q : impure i a) (equ : p == q) (sem : semantics i)
  : run_impure sem p == run_impure sem q.
Proof.
  now rewrite equ.
Qed.

Hint Resolve run_impure_equiv : freespec.

Lemma run_impure_exec_impure_equiv {i a}
  (sem sem' : semantics i) (p q : impure i a) (equ : run_impure sem p == run_impure sem' q)
  : exec_impure sem p == exec_impure sem' q.
Proof.
  now inversion equ; ssubst.
Qed.

Hint Resolve run_impure_exec_impure_equiv : freespec.

Lemma run_impure_eval_impure_equiv {i a}
  (sem sem' : semantics i) (p q : impure i a) (equ : run_impure sem p == run_impure sem' q)
  : eval_impure sem p = eval_impure sem' q.
Proof.
  now inversion equ; ssubst.
Qed.

Hint Resolve run_impure_eval_impure_equiv : freespec.

Lemma exec_impure_equiv {i a} (p q : impure i a) (equ : p == q) (sem : semantics i)
  : exec_impure sem p == exec_impure sem q.
Proof.
  now rewrite equ.
Qed.

Hint Resolve run_impure_equiv : freespec.

Lemma impure_bind_equation {i a b}
  (p : impure i a) (f : a -> impure i b) (sem : semantics i)
  : run_impure sem (impure_bind p f)
    == run_impure (exec_impure sem p) (f (eval_impure sem p)).
Proof.
  revert sem.
  induction p; intros sem.
  + reflexivity.
  + cbn.
    apply H.
Qed.

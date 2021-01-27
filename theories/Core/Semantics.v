(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(** In FreeSpec, there is no particular semantics attach to interface's
    primitives. Once an interface has been defined, we can provide one (or
    more) operational semantics to interpret its primitives. *)

(** * Definition *)

(** An operational [semantics] for the interface [i] is coinductively defined as
    a function which can be used to interpret any primitive of [i]; it produces
    an [interp_out] term. *)

From Coq Require Import Program Setoid Morphisms.
From ExtLib Require Import Monad StateMonad.
From FreeSpec.Core Require Export Interface Impure.

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

(** Besides, and similarly to interfaces, operational semantics can and should
    be composed together.  To that end, we provide the [semprod] operator. *)

CoFixpoint semprod {i j} (sem_i : semantics i) (sem_j : semantics j)
  : semantics (i + j) :=
  mk_semantics (fun _ e =>
                  match e with
                  | in_left e =>
                    let (x, out) := run_effect sem_i e in
                    (x, semprod out sem_j)
                  | in_right e =>
                    let (x, out) := run_effect sem_j e in
                    (x, semprod sem_i out)
                  end).

Declare Scope semantics_scope.
Bind Scope semantics_scope with semantics.
Delimit Scope semantics_scope with semantics.

Infix "*" := semprod : semantics_scope.

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

Notation interp i := (state (semantics i)).

Definition interface_to_state {i} : i ~> interp i :=
  fun a e => mkState (fun sem => run_effect sem e).

Definition to_state {i} : impure i ~> state (semantics i) :=
  impure_lift interface_to_state.

Arguments to_state {i α} _.

Definition run_impure {i a} (sem : semantics i) (p : impure i a) : a * semantics i :=
  runState (to_state p) sem.

Definition eval_impure {i a} (sem : semantics i) (p : impure i a) : a :=
  fst (run_impure sem p).

Definition exec_impure {i a} (sem : semantics i) (p : impure i a) : semantics i :=
  snd (run_impure sem p).

(** * In-place Primitives Handling *)

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

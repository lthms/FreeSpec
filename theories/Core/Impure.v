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

(** In [FreeSpec.Core.Interface], we have introduced the [interface] type, to
    model the set of primitives an impure computation can use. We also introduce
    [MayProvide], [Provide] and [Distinguish]. They are three type classes which
    allow for manipulating _polymorphic interface composite_.


    In this library, we provide the [impure] monad, defined after the
    <<Program>> monad introduced by the <<operational>> package (see
    <<https://github.com/whitequark/unfork#introduction>>). *)

From Coq Require Import Program Setoid Morphisms.
From ExtLib Require Export MonadState.
From FreeSpec.Core Require Export Interface Lifter.

(** We introduce the [impure] monad to describe impure computations, that is
    computations which uses primitives from certain interfaces. *)

(** * Definition *)

(** The [impure] monad is an inductive datatype with two parameters: the
    interface [i] to be used, and the type [α] of the result of the computation.
    The fact that [impure] is inductive rather than co-inductive means it is not
    possible to describe infinite computations.  This also means it is possible
    to interpret impure computations within Coq, providing an operational
    semantics for [i]. *)

Inductive impure (i : interface) (α : Type) : Type :=
| local (x : α) : impure i α
| request_then {β} (e : i β) (f : β -> impure i α) : impure i α.

Arguments local [i α] (x).
Arguments request_then [i α β] (e f).

Register impure as freespec.core.impure.type.
Register local as freespec.core.impure.local.
Register request_then as freespec.core.impure.request_then.

Declare Scope impure_scope.
Bind Scope impure_scope with impure.
Delimit Scope impure_scope with impure.

(** * Monad Instances *)

(** We then provide the necessary instances of the <<coq-prelude>> Monad
    typeclasses hierarchy. *)

Fixpoint impure_bind {i α β} (p : impure i α) (f : α -> impure i β) : impure i β :=
  match p with
  | local x => f x
  | request_then e g => request_then e (fun x => impure_bind (g x) f)
  end.

Definition impure_map {i α β} (f : α -> β) (p : impure i α) : impure i β :=
  impure_bind p (fun x => local (f x)).

Instance impure_Functor : Functor (impure i) :=
  { fmap := @impure_map i
  }.

Definition impure_pure {i α} (x : α) : impure i α := local x.

Definition impure_apply {i α β} (p : impure i (α -> β)) (q : impure i α) : impure i β :=
  impure_bind p (fun f => fmap f q).

Instance impure_Applicative : Applicative (impure i) :=
  { pure := @impure_pure i
  ; ap := @impure_apply i
  }.

Instance impure_Monad (i : interface) : Monad (impure i) :=
  { ret := @impure_pure i
  ; bind := @impure_bind i
  }.

(** * Defining Impure Computations *)

(** FreeSpec users shall not use the [impure] monad constructors directly.  The
    [pure] function from the [Applicative] typeclass allows for defining pure
    computations which do not depend on any impure primitive.  The [bind]
    function from the [Monad] typeclass allows for seamlessly combine impure
    computations together.

    To complete these two monadic operations, we introduce the [request]
    function, whose purpose is to define an impure computation that uses a given
    primitive [e] from an interface [i], and returns its result.  [request] does
    not parameterize the [impure] monad with [i] directly, but rather with a
    generic interface [ix].  [ix] is constrained with the [Provide] notation, so
    that it has to provide at least [i]'s primitives.  *)

Definition request `{Provide ix i} {α} (e : i α) : impure ix α :=
  request_then (inj_p e) (fun x => pure x).

(** Note: there have been attempts to turn [request] into a typeclass
    function (to seamlessly use [request] with a [MonadTrans] instance such as
    [state_t]). The reason why it has not been kept into the codebase is that
    the flexibility it gives for writing code has a real impact on the
    verification process. It is simpler to reason about “pure” impure
    computations (that is, not within a monad stack), then wrapping these
    computations thanks to [lift].

    The <<coq-prelude>> provides notations (inspired by the do notation of
    Haskell) to write monadic functions more easily.  These notations live
    inside the [monad_scope]. *)

Instance store_monad_state (s : Type) (ix : interface) `{Provide ix (STORE s)}
  : MonadState s (impure ix) :=
  { put := fun (x : s) => request (Put x)
  ; get := request Get
  }.

(** * Lift *)

Definition impure_lift `{Monad m} `(l : i ~> m) : impure i ~> m :=
  fix aux a (p : impure i a) :=
    match p with
    | local x => ret x
    | request_then e f => let* x := l _ e in aux a (f x)
    end.

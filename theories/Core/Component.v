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

From ExtLib Require Import StateMonad.
From FreeSpec.Core Require Export Interface Semantics Impure.

(** * Definition *)

(** In FreeSpec, a _component_ is an entity which exposes an interface [i],
    and uses primitives of an interface [j] to compute the results of primitives
    of [i].  Besides, a component is likely to carry its own internal state (of
    type [s]).

<<
                           i +-------------------+      j
                           | |                   |      |
                   +------>| | c : component i j |----->|
                           | |                   |      |
                             +-------------------+
>>

    Thus, a component [c : component i j] is a polymorphic function which
    maps primitives of [i] to impure computations using [j]. *)

Definition component (i j : interface) : Type :=
  forall (α : Type), i α -> impure j α.

(** The similarity between FreeSpec components and operational semantics may be
    confusing at first. The main difference between the two concepts is simple:
    operational semantics are self-contained terms which can, alone, be used to
    interpret impure computations of a given interface.  Components, on the
    other hand, are not self-contained.  Without an operational semantics for
    [j], we cannot use a component [c : component i j] to interpret an impure
    computation using [i].

    Given an initial semantics for [j], we can however derive an operational
    semantics for [i] from a component [c]. *)

(** * Semantics Derivation *)

CoFixpoint derive_semantics {i j} (c : component i j) (sem : semantics j)
  : semantics i :=
  mk_semantics (fun a p =>
                  let (res, next) := runState (to_state $ c a p) sem in
                  (res, derive_semantics c next)).

(** So, [semprod] on the one hand allows for composing operational semantics
    horizontally, and [derive_semantics] allows for composing components
    vertically.  Using these two operators, we can model a complete system in a
    hierarchical and modular manner, by defining each of its components
    independently, then composing them together with [semprod] and
    [derive_semantics]. *)

Definition bootstrap {i} (c : component i iempty) : semantics i :=
  derive_semantics c iempty_semantics.

(** * In-place Primitives Handling *)

(** The function [with_component] allows for locally providing an additional
    interface [j] within an impure computation of type [impure ix a]. The
    primitives of [j] will be handled by impure computations, i.e., a component.
    of type [c : compoment j ix s]. *)

#[local]
Fixpoint with_component_aux {ix j α} (c : component j ix) (p : impure (ix + j) α)
  : impure ix α :=
  match p with
  | local x => local x
  | request_then (in_right e) f =>
    c _ e >>= fun res => with_component_aux c (f res)
  | request_then (in_left e) f =>
    request_then e (fun x => with_component_aux c (f x))
  end.

Definition with_component {ix j α}
  (initializer : impure ix unit)
  (c : component j ix)
  (finalizer : impure ix unit)
  (p : impure (ix + j) α)
  : impure ix α :=
  initializer;;
  let* res := with_component_aux c p in
  finalizer;;
  pure res.

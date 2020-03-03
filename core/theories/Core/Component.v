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

From FreeSpec.Core Require Import Interface Semantics Impure.

(** * Component

    In FreeSpec, a _component_ is an entity which exposes an interface [i],
    and uses primitives of an interface [j] to compute the results of primitives
    of [i].  Besides, a component is likely to carry its own internal state (of
    type [s]).

<<
                               c : component i j s
                           i +---------------------+      j
                           | |                     |      |
                   +------>| |       st : s        |----->|
                           | |                     |      |
                             +---------------------+
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

CoFixpoint derive_semantics {i j} (c : component i j) (sem : semantics j)
  : semantics i :=
  mk_semantics (fun _ p =>
                  let run := run_impure sem (c _ p) in
                  let res := interp_result run in
                  let next := interp_next run in
                  mk_out res (derive_semantics c next)).

(** So, [⊕] on the one hand allows for composing operational semantics
    horizontally, and [derive_semantics] allows for composing components
    vertically.  Using these two operators, we can model a complete system in a
    hierarchical and modular manner, by defining each of its components
    independently, then composing them together with [⊕] and
    [derive_semantics]. *)

Definition bootstrap {i} (c : component i iempty) : semantics i :=
  derive_semantics c iempty_semantics.

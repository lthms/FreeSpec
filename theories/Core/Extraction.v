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

From FreeSpec Require Import Core.

(** FreeSpec has been designed from the start to be compatible with
    the extraction mechanism of Coq. That being said, this approach is
    no longer the preferred one, and we now advice to write your
    impure programs in a polymorphic monad, which is specialized in a
    [IO]-like monad (such as the one introduced by the
    <<coq-simple-io>> package) for extraction, and [impure] for formal
    verification. *)

(** * How to *)

(** To get an executable program from an impure program [p]
    implemented in the [impure] monad parameterized by an interface
    [i], the approach is to define a function (said, [main]) whose
    body is of the form [run_impure ocaml_sem p], where [ocaml_sem] is
    a semantics for [i].

    More precisely, for each constructor of [i], there should be an
    ocaml functions that can be called to handle it. These functions
    can be made available to Coq modules by (1) introducing an axiom,
    and (2) configuring the extraction mechanism accordingly.

    Once this is done, one can call [Recursive Extraction main]. *)

(** * Extraction Configuration *)

(** The extraction mechanism of Coq suffers, sadly, long standing
    bugs. These bugs prevents the extracted OCaml code to compile.
    Fortunately, these bugs can be avoided by inlining certain key
    definitions. Note that, at the time of writing this documentation,
    this approach does sadly not work with the [Recursive Extraction
    Library] command. *)

Extraction Inline impure_Applicative.

From CoqFFI Require Import Interface.

Instance FreeSpec_Inject `(H : Provide ix i) : Inject i (impure ix) :=
  { inject := @request ix i _ H }.

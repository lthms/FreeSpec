(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

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

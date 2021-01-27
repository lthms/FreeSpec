(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From FreeSpec.Core Require Export Core.

(** This module loads a Coq plugin which provides the [Exec]
    vernacular command. [Exec] is analogous to [Compute], but works
    with [impure] terms. [Exec] uses the Coq reduction engine to make
    the head constructor of the term provided as argument for [Exec]
    appears. Then, in presence of the [request_then] constructor, it
    uses handler functions provided by FreeSpec users to perform the
    impure tasks and compute a result. This result is passed to the
    continuation, and the [Exec] interpreter is recursively
    called. When the constructor is [local], the computation is
    completed.

    By default, [Exec] uses a reduction strategy analogous to
    [cbn]. It also accepts the <<nf>> attribute to change this
    behavior, and prefers an approach analogous to
    <<compute>>. Changing the reduction strategy can be handy in
    presence of a term which takes a very long time to reduce with
    <<cbn>>. This is typically the case with terms that relies on
    well-founded recursion rather than structural recursion. *)

From CoqFFI Require Import Int.

(* Import necessary types. *)

From FreeSpec.Exec Require Import Eval.
From FreeSpec.FFI Require Import FFI Refs ML.

From Coq Require Import String Ascii Byte.

(** * Extending FreeSpec.Exec *)

(** The FreeSpec.Exec plugin has been designed to be extensible, meaning it
    shall be easy for FreeSpec users to provide handlers for their own
    interfaces.

    In FreeSpec, primitives are modeled with Coq constructors of an [interface]
    inductive type. FreeSpec.Exec allows to define so-called
    <<effectful_semantic>> for these constructors which aim to compute the
    related primitive results.

    The OCaml type <<effectful_semantic>> is defined as follows:

<<
type effectful_semantic =
  Constr.constr list -> Constr.constr
>>

    If you are not familiar with Coq internals, <<Constr.constr>> is the
    representation of Coq terms. Therefore, an <<effectful_semantic>> is an
    OCaml function which maps a list of Coq terms (the arguments of the
    primitives) to its result.

    For instance, if we consider the following interface:

<<
Inductive CONSOLE : interface :=
| WriteLine : string -> CONSOLE unit
| ReadLine : CONSOLE string.
>>

    Since <<Coq-8.10>>, it is required to manually register both the type of an
    interface and its constructors for plugins to easily interact with them. This is done
    with the [Register] command.

<<
Register <Coq Name> <Unique ID>.
>>

    The <<FreeSpec.Exec>> plugin expects the unique ID to be of the form <<<some
    path>.<Coq Name> >>for contructors and <<<some path>.type>> for the type. In
    the case of the <<CONSOLE>> interface, we could use:

<<
Register CONSOLE freespec.exec.console.type.
Register WriteLine freespec.exec.console.WriteLine.
Register ReadLine freespec.exec.console.ReadLine.
>>

    Then, one can implement two <<effectful_semantic>>: one for the constructor
    <<WriteLine>> and the other for the constructor <<ReadLine>>:

<<
let writeline = function
  | [str] -> print_bytes (bytes_of_coqstr str);
             coqtt
  | _ -> assert false

let readline = function
  | [] -> string_to_coqstr (read_line ())
  | _ -> assert false
>>

    There are several facts to explain.

    First, manipulating <<Constr.constr>> value manually shall not be required
    most of the time, since the FreeSpec.Exec plugin provides several helpers
    isomorphisms to turn Coq term into OCaml values and vice-versa.
    Hence, <<bytes_of_coqstr>> translates a [string] term into a [bytes] value,
    while <<string_to_coqstr>> translates a OCaml [string] value into a Coq
    [string] term.

    Secondly, it is the responsibility of plugin developers to ensure they
    consider the right number of arguments for their <<effectful_semantic>>. The
    <<WriteLine>> constructor has one argument, so the <<writeline>> OCaml
    function only considers one-element lists. The <<ReadLine>> constructor has
    no argument, so the <<readline>> OCaml function only handles the empty list.

    Thirdly, it is also the responsibility of plugin developers to forge a
    well-typed result for their primitives.

    Once the <<effectful_semantic>> have been defined, they need to be
    registered to FreeSpec.Exec, so that the plugin effectively use them. The
    <<Extends>> OCaml module of FreeSpec.Exec provides a function to that hand:

<<
val register_interface :
  (* The base path we have chosen to register our interface. *)
     string
  (* A list to map each constructor of this interface
     to an effectful semantic. *)
  -> (string * effectful_semantic) list
  -> unit
>>

    It shall be used as follows:

<<
let _ =
  register_interface
    "freespec.exec.console"
    [("WriteLine", writeline); ("ReadLine", readline)]
>> *)

(* TODO: this shall be in the standard library of Coq *)
Register byte as coq.byte.type.
(* end TODO *)

Register REFS as freespec.ffi.REFS.type.
Register Make_ref as freespec.ffi.REFS.Make_ref.
Register Assign as freespec.ffi.REFS.Assign.
Register Deref as freespec.ffi.REFS.Deref.

Declare ML Module "freespec_exec".

(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2019 Thomas Letan <thomas.letan@ssi.gouv.fr>
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

From FreeSpec Require Export Core.
From FreeSpec.Exec Require Export Debug Eval.

(* TODO: this shall be in the standard library of Coq *)
Register unit as core.unit.type.
Register tt as core.unit.tt.

Register pair as core.prod.pair.
Register sum as core.sum.type.
Register inl as core.sum.inl.
Register inr as core.sum.inr.

From Coq Require Import String Ascii Int63 Byte.
From Prelude Require Import Bytes.

Register string as plugins.syntax.string.type.
Register EmptyString as plugins.syntax.string.EmptyString.
Register String as plugins.syntax.string.String.

Register ascii as plugins.syntax.ascii.type.
Register Ascii as plugins.syntax.ascii.Ascii.

Register byte as coq.byte.type.
(* end TODO *)

Declare ML Module "freespec_exec".

(** * Extending FreeSpec.Exec *)

(** The FreeSpec.Exec plugin has been designed to be extensible, meaning it
    shall be easy for FreeSpec users to provide handlers for their own
    interfaces. *)

(** ** By Means of OCaml plugins

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
>>

    For a concrete example of the use of FreeSpec.Exec extensible feature,
    interested readers can have a look at the FreeSpec.Stdlib project in the
    <<stdlib/>> folder of this repository. *)

(** ** By Means of Compoments *)

(** The second way to extend FreeSpec.Exec is to write handlers in Coq, in the
    form of FreeSpec compoments. This approach has an important advantage over
    writing an OCaml plugin: it is possible to verify a FreeSpec
    [component]. However, we foresee an impact over the resulting program
    performances.

    The function [with_component] allows for locally providing a novel interface
    [j] in addition to an impure computation [p], by means of a FreeSpec
    component [c : compoment j ix s].  Two impure computations have to be
    provided: [initializer] to create the initial state of [c], and [finalizer]
    to clean-up the final state of [c] after the interpretation of [p]. *)

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
  do initializer;
     let* res := with_component_aux c p in
     finalizer;
     pure res
  end.

#[local]
Fixpoint with_semantics {ix j α} (sem : semantics j) (p : impure (ix + j) α)
  : impure ix α :=
  match p with
  | local x => local x
  | request_then (in_right e) f =>
    let run := run_effect sem e in
    let res := interp_result run in
    let next := interp_next run in
    with_semantics next (f res)
  | request_then (in_left e) f =>
    request_then e (fun x => with_semantics sem (f x))
  end.

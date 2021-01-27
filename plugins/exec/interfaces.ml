(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

open Utils

(**

   The OCaml interpretation of an effectful primitive is an
   effectful OCaml function from Coq terms to Coq term.

*)
type effectful_semantic = Constr.constr list -> Constr.constr

let primitive_semantics : effectful_semantic Names.Constrmap.t ref =
  ref Names.Constrmap.empty

let new_primitive m c p =
  match Coqlib.lib_ref (m ^ "." ^ c) with
    | Names.GlobRef.ConstructRef c ->
       primitive_semantics := Names.Constrmap.add c p !primitive_semantics
    | _ ->
       invalid_arg "Only constructor can identify primitives."

let primitive_semantic : Names.constructor -> effectful_semantic =
  fun c -> try
    Names.Constrmap.find c !primitive_semantics
  with Not_found -> raise UnsupportedInterface

(**

   An initializer binds the constructor identifier of the interface
   request to an OCaml function that implements its semantics.

   To register a new interface, a plugin must install an initializer
   that will be triggered at [Exec] time. The initializer cannot be
   run at [Declare Module] time because the identifiers of the
   constructors might not be properly bound in Coq environment at this
   moment.

*)

(** A queue for initializers to be triggered at [Exec] time. *)
let initializers = Queue.create ()

(** [add_register_handler i]. *)
let add_register_handler interface_initializer =
  Queue.add interface_initializer initializers

(** [force_interface_initializers ()] initialize the interfaces that
    have been registered by [register_interfaces]. *)
let force_interface_initializers () =
  Queue.(
    while not (is_empty initializers) do
      pop initializers ()
    done
  )

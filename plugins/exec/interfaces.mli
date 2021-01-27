(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

type effectful_semantic = Constr.constr list -> Constr.constr

val new_primitive: string -> string -> effectful_semantic -> unit
val primitive_semantic : Names.constructor -> effectful_semantic

val force_interface_initializers: unit -> unit
val add_register_handler: (unit -> unit) -> unit

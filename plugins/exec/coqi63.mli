(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

val int_of_coqint : Constr.constr -> int
val int_to_coqint : int -> Constr.constr

val int_of_coqi63 : Constr.constr -> int
val int_to_coqi63 : int -> Constr.constr

val coqi63_t : Constr.constr

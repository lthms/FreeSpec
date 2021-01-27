(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

val char_of_coqbyte : Constr.constr -> char
val char_to_coqbyte : char -> Constr.constr

val coqbyte_t : Constr.constr

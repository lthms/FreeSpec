(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

type ('a, 'b) sum = Left of 'a | Right of 'b

val sum_of_coqsum : (Constr.constr -> 'a) -> (Constr.constr -> 'b) -> Constr.constr -> ('a, 'b) sum
val sum_to_coqsum : Constr.constr -> ('a -> Constr.constr) -> Constr.constr -> ('b -> Constr.constr) -> ('a, 'b) sum -> Constr.constr

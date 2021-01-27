(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

val prod_of_coqprod : (Constr.constr -> 'a) -> (Constr.constr -> 'b) -> Constr.constr -> ('a * 'b)
val prod_to_coqprod :
  Constr.constr -> ('a -> Constr.constr) -> Constr.constr -> ('b -> Constr.constr) -> ('a * 'b) -> Constr.constr

val coqprod_t : Constr.constr -> Constr.constr -> Constr.constr

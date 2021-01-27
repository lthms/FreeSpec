(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

open Query
open Utils

let int_of_coqint coqint =
  match Constr.kind coqint with
  | Constr.Int i -> snd (Uint63.to_int2 i)
  | _ -> raise (UnsupportedTerm "Not a native integer")

let int_to_coqint v = Constr.(of_kind (Int (Uint63.of_int v)))

let int_of_coqi63 trm =
  let (c, args) = app_full trm in
  match (Ind.I63.constructor_of c, args) with
  | (Some Mk_i63, [trm]) -> int_of_coqint trm
  | _ -> raise (UnsupportedTerm "int_of_coqi63")

let int_to_coqi63 n =
  let trm = int_to_coqint n in
  Constr.mkApp (Ind.I63.mkConstructor "mk_i63", Array.of_list [trm])

let coqi63_t = Ind.I63.mkInductive

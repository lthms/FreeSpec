(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

open Query
open Utils

let bool_of_coqbool cbool =
  match Ind.Bool.constructor_of cbool with
  | Some b -> b
  | _ -> raise (UnsupportedTerm "not a [bool] constructor")

let bool_to_coqbool = function
  | true -> Ind.Bool.mkConstructor "true"
  | false -> Ind.Bool.mkConstructor "false"

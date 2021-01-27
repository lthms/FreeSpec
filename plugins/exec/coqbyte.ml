(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

open Constr
open Query
open Utils

let char_of_coqbyte trm =
  match kind trm with
  | Construct ((_, x), _) -> Char.chr (x - 1) (* constructor indexes start at 1 *)
  | _ -> raise (UnsupportedTerm "not a Byte")

let char_to_coqbyte c =
  match kind Ind.Byte.mkInductive with
  | Ind (i, _) -> Constr.mkConstruct (i, 1 + Char.code c)
  | _ -> assert false

let coqbyte_t = Ind.Byte.mkInductive

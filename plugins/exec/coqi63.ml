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

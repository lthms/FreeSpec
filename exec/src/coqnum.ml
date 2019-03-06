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
open Constr

let int_of_coqpositive =
  let rec of_coqpositive_aux acc depth p =
    let (p, args) = app_full p in
    match kind p with
    | Construct (p, _)
      -> (match (Ind.Positive.constructor_of p, args) with
          | (Some XH_positive, []) -> acc + depth
          | (Some XO_positive, [next]) -> of_coqpositive_aux acc (2 * depth) next
          | (Some XI_positive, [next]) -> of_coqpositive_aux (acc + depth) (2 * depth) next
          | _ -> raise (UnsupportedTerm "not a constructor of [positive]"))
    | _ -> raise (UnsupportedTerm "not a constructor of [positive]")
  in of_coqpositive_aux 0 1

let int_to_coqpositive =
  raise (UnsupportedTerm "To be implemented")

let int_of_coqz z =
  let (z, args) = app_full z in
  match kind z with
  | Construct (z, _)
    -> (match (Ind.Z.constructor_of z, args) with
        | (Some Z0_Z, []) -> 0
        | (Some Zpos_Z, [p]) -> int_of_coqpositive p
        | (Some Zneg_Z, [p]) -> -1 * int_of_coqpositive p
        | _ -> raise (UnsupportedTerm "not a constructor of [Z]"))
  | _ -> raise (UnsupportedTerm "not a constructor of [Z]")


let int_to_coqz =
  raise (UnsupportedTerm "To be implemented")

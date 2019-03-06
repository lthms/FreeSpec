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

let bool_of_coqbool cbool =
  match kind cbool with
  | Construct (c, _) ->
     (match Ind.Bool.constructor_of c with
      | Some b -> b
      | _ -> raise (UnsupportedTerm "not a [bool] constructor"))
  | _ -> raise (UnsupportedTerm "not a constructor")

let bool_to_coqbool = function
  | true -> Ind.Bool.mkConstructor "true"
  | otherwise -> Ind.Bool.mkConstructor "false"

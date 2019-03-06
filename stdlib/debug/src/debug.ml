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

open Exec_plugin.Coqstr
open Exec_plugin.Coqbool
open Exec_plugin.Coqnum
open Exec_plugin.Interfaces
open Exec_plugin.Query
open Exec_plugin.Utils
open Constr

let path = ["FreeSpec"; "Stdlib"; "Debug"; "Debug"]

let install_interfaces = register_interfaces @@ fun () -> (
  new_primitive path "Inspect" (function [term_type; _instance; term] ->
     (match kind term_type with
      | Ind (t, _)
        -> if Ind.Z.ref_is t
           then print_int (int_of_coqz term)
           else if Ind.Positive.ref_is t
           then print_int (int_of_coqpositive term)
           else if Ind.Bool.ref_is t
           then print_string (if (bool_of_coqbool term) then "true" else "false")
           else if Ind.Ascii.ref_is t
           then print_char (char_of_coqascii term)
           else if Ind.String.ref_is t
           then print_string (str_of_coqstr term)
           else raise (UnsupportedTerm "There is no available isomorphism for this type");
           Ind.Unit.mkConstructor "tt"
      | _
        -> raise (UnsupportedTerm "There is no available isomorphism for this type"))
  | _ -> assert false);
)

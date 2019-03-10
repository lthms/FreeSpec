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

open Coqstr
open Coqbool
open Coqnum
open Extends
open Query
open Utils

let path = ["FreeSpec"; "Exec"; "Debug"; "Debug"]

let map_iso_type term_type term fint fbool fchar fstring =
  if Ind.Z.ref_is term_type
  then fint (int_of_coqz term)
  else if Ind.Bool.ref_is term_type
  then fbool (bool_of_coqbool term)
  else if Ind.Ascii.ref_is term_type
  then fchar (char_of_coqascii term)
  else if Ind.String.ref_is term_type
  then fstring (bytes_of_coqstr term)
  else raise (UnsupportedTerm "There is no available isomorphism for this type")

let install_debug_interface =
  let inspect = function
    | [term_type; _instance; term]
      -> let str = map_iso_type
                     term_type
                     term
                     string_of_int
                     string_of_bool
                     (String.make 1)
                     Bytes.to_string
         in string_to_coqstr str
    | _ -> assert false in
  let iso = function
    | [term_type; _instance; term]
      -> let cstr = map_iso_type
                      term_type
                      term
                      int_to_coqz
                      bool_to_coqbool
                      char_to_coqascii
                      bytes_to_coqstr
         in cstr
    | _ -> assert false in
  register_interface path [("Inspect", inspect); ("Iso", iso)]

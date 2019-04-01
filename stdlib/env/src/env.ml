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
open Exec_plugin.Extends
open Exec_plugin.Coqunit

let path = ["FreeSpec"; "Stdlib"; "Env"; "Env"]

let install_interface =
  let get = function
    | [var]
      -> let str = try
             Unix.getenv (string_of_coqstr var)
           with
           | _ -> ""
         in string_to_coqstr str
    | _
      -> assert false in
  let set = function
    | [var; value]
      -> Unix.putenv (string_of_coqstr var) (string_of_coqstr value);
         coqtt
    | _ -> assert false
  in register_interface path [("GetVar", get); ("SetVar", set)]

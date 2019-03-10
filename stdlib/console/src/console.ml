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
open Exec_plugin.Query

let path = ["FreeSpec"; "Stdlib"; "Console"; "Console"]

let install_interface =
  let scan = function
    | [] -> string_to_coqstr (read_line ())
    | _ -> assert false in
  let echo = function
    | [str] -> print_bytes (bytes_of_coqstr str);
               Ind.Unit.mkConstructor "tt"
    | _ -> assert false in
  register_interface path [("Scan", scan); ("Echo", echo)]

(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2019 Vincent Tourneur <vincent.tourneur@inria.fr>
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
open Exec_plugin.Coqnum

let path = ["FreeSpec"; "Stdlib"; "CommandLine"; "CommandLine"]

let install_interface =
  let argc = function
    | [] -> int_to_coqz (int_of_string (Sys.getenv "FREESPEC_RUN_ARGC"))
    | _ -> assert false in
  let arg = function
    | [n] -> string_to_coqstr (Sys.getenv ("FREESPEC_RUN_ARG_" ^ (string_of_int (int_of_coqz n))))
    | _ -> assert false in
  register_interface path [("Argc", argc); ("Arg", arg)]

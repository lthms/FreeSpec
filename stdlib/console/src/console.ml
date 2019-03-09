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
open Exec_plugin.Interfaces
open Exec_plugin.Query


let scan = read_line
let echo = print_bytes

let path = ["FreeSpec"; "Stdlib"; "Console"; "Console"]

let install_interfaces = register_interfaces @@ fun () -> (
  new_primitive path "Scan" (function [] ->
    bytes_to_coqstr (Bytes.of_string @@ scan ())
  | _ -> assert false);

  new_primitive path "Echo" (function [str] ->
    echo (bytes_of_coqstr str);
    Ind.Unit.mkConstructor "tt"
  | _ -> assert false)
)

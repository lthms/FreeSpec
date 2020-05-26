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

open Coqbase
open Freespec_exec.Coqbytestring
open Freespec_exec.Extends
open Freespec_exec.Coqunit

let path = "freespec.stdlib.env"

let install_interface =
  let get = function
    | [var]
      -> let str = try Unix.getenv (Bytestring.to_string (bytestring_of_coqbytestring var))
                   with _ -> ""
         in bytestring_to_coqbytestring (Bytestring.of_string str)
    | _
      -> assert false in
  let set = function
    | [var; value]
      -> Unix.putenv
           (Bytestring.to_string @@ bytestring_of_coqbytestring var)
           (Bytestring.to_string @@ bytestring_of_coqbytestring value);
         coqtt
    | _ -> assert false
  in register_interface path [("GetEnv", get); ("SetEnv", set)]

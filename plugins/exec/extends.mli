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

(** Extend FreeSpec.Exec by associating primitives constructor names to
    effectful semantics. *)

val register_interface: string -> (string * Interfaces.effectful_semantic) list -> unit
(** After [register_interface modpath [(cname1, sem1); ...; (cnamen, semn)]] has
    been executed, primitives constructed with constructors [cname1] to [cnamen]
    (which lives in the module defined by [modpath]) will be supported by the
    [Exec] command, which will use [sem1] to [semn] to realize them.

    To illustrate how [register_interface] is used, we can take the example of
    the [Console.i] interface. [Console.i] constructor live in the
    [FreeSpec.Stdlib.Console.Console] module, which translate in OCaml into
    [["FreeSpec"; "Stdlib"; "Console"; "Console"]].

    Therefore, extending FreeSpec.Exec to support [Console.i] primitives becomes
    as simple as:

    {[
let _ =
  register_interface
    ["FreeSpec"; "Stdlib"; "Console"; "Console"]
    [("Scan", scan); ("Echo", echo)]
    ]} *)

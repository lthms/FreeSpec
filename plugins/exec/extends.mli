(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

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

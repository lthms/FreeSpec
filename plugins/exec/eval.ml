(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

open Extends

let path = "freespec.exec.eval"

let install_interface =
  register_interface path [
      ("Eval", function | [_typ; trm] -> trm
                        | _ -> assert false)
    ]

(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

open Interfaces

let register_interface path semantics =
  let reg _ = function
      | (name, sem) -> new_primitive path name sem
  in
  add_register_handler @@ fun _ -> List.fold_left reg () semantics

(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

exception Anomaly of string
exception UnsupportedTerm of string
exception UnsupportedInterface
exception NotImplementedYet

let notice str =
  Feedback.msg_notice (Pp.strbrk str)

let app_full trm =
  let rec aux trm acc =
    match Constr.kind trm with
    | Constr.App (f, xs)
      -> aux f (Array.to_list xs @ acc)
    | _
      -> (trm, acc)
  in aux trm []

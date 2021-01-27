(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

let vault : Obj.t Store.t = Store.create ()

let insert v = Store.add vault (Obj.repr v)
let remove = Store.remove vault
let replace k v = Store.replace vault k (Obj.repr v)
let find k = Obj.obj (Store.find vault k)

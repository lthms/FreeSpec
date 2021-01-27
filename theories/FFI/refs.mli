(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

type 'a reference = 'a ref

val make_ref : 'a -> 'a reference [@@impure]
val deref : 'a reference -> 'a [@@impure]
val assign : 'a reference -> 'a -> unit [@@impure]

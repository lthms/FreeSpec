(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

type 'a t

val create : unit -> 'a t
val add : 'a t -> 'a -> Constr.t
val remove : 'a t -> Constr.t -> unit
val find : 'a t -> Constr.t -> 'a
val replace : 'a t -> Constr.t -> 'a -> unit

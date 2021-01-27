(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

val insert : 'a -> Constr.t
val replace : Constr.t -> 'a -> unit
val find : Constr.t -> 'a
val remove : Constr.t -> unit

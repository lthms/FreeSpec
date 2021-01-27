(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(** This module provides the means to encode a form of “pointers” in Coq. See
    the [HEAP] interface for more information about how to use it in a Coq
    program. *)

val make_ref : Constr.t -> Constr.t
(** Store a Coq term inside the so-called heap, and return a reference to
    manipulate it. *)

val destruct : Constr.t -> unit
(** Remove the Coq term identified by the reference passed as an argument from
    the so-called heap. This means [deref] and [assign] will not work with this
    reference afterards. *)

val deref : Constr.t -> Constr.t
(** Return the Coq term identified by the reference passed as an argument. *)

val assign : Constr.t -> Constr.t -> unit
(** Change the Coq term identified by the reference passed as an argument. This
    means that after the evaluation of [assign r v], [deref r] returns [v]. *)

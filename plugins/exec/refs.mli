(* FreeSpec
 * Copyright (C) 2018–2020 ANSSI
 *
 * Contributors:
 * 2020 Thomas Letan <thomas.letan@ssi.gouv.fr>
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

(** This module provides the means to encode a form of “pointers” in Coq. See
    the [HEAP] interface for more information about how to use it in a Coq
    program. *)

val new_ref : Constr.t -> Constr.t
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

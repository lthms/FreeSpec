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

val coqfd_t : Constr.constr

(** Add an OCaml file descriptor to the resource manager, and create a Coq term
    to manipulate it later.

    After the execution of [make_coqfd fd], the file descriptor [fd] is being
    stored in FreeSpec.Exec resource manager. The Coq term returned by the
    function is a Coq native integer whose value is [fd]'s key chosen by the
    resource manager.

    This function should only be called once, for fresh file descriptors created
    by functions like [open]. Currently, there is no way to retrieve the Coq
    term associated with a file descriptor already open. *)

val make_coqfd : Unix.file_descr -> Constr.t

(** Remove an OCaml file descriptor identified by the given Coq native integer
    from the resource manager contents.

    This function expects its first argument to be a Coq native integer. This is
    potentially unsafe if the key used has been freed or has not been used to
    store a file descriptor, but something else. The file descriptor removed
    from the resource manager is returned. *)

val destruct_coqfd : Constr.t -> Unix.file_descr

(** Retrieve the OCaml file descriptor associated with a given Coq native
    integer.

    This function expects its first argument to be a Coq native integer. It uses
    this integer as a key for the resource manager, to retrieve a file
    descriptor previously stored using this key. This is potentially unsafe if
    the key used has been freed or has not been used to store a file descriptor,
    but something else. *)

val fd_of_coqfd : Constr.t -> Unix.file_descr

val int_to_files_err : int -> Constr.constr
val to_files_res : Constr.constr -> ('a -> Constr.constr) -> (int, 'a) Freespec_exec.Coqsum.sum -> Constr.constr

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

open Array
open Freespec_exec
open Freespec_exec.Query
open Freespec_exec.Coqnum
open Freespec_exec.Coqsum

type files_err_constructor = Make_files_err_constructor

let coqfd_t =
  match Coqlib.lib_ref "freespec.stdlib.file_descriptor.type" with
  | Names.GlobRef.ConstRef c -> Constr.mkConst c
  | _ -> raise (Utils.Anomaly "Could not construct the type int")

module FilesErr =
    Inductive.Make(struct
        type constructor = files_err_constructor
        let type_name = "files_err"
        let namespace = "freespec.stdlib.files_err"
        let names = [("make_files_err", Make_files_err_constructor)]
      end)

let make_coqfd fd = Resources.insert fd

let destruct_coqfd coqfd =
  let x = Resources.find coqfd in
  Resources.remove coqfd;
  x

let fd_of_coqfd = Resources.find

let int_to_files_err x =
  Constr.mkApp (FilesErr.mkConstructor "make_files_err", of_list [int_to_coqint x])

let to_files_res typ to_coq trm =
  sum_to_coqsum FilesErr.mkInductive int_to_files_err typ to_coq trm

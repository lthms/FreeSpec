(* FreeSpec
 * Copyright (C) 2018–2020 ANSSI
 *
 * Contributors:
 * 2019 Thomas Letan <thomas.letan@ssi.gouv.fr>
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

open Freespec_exec.Extends
open Freespec_exec.Coqstr
open Freespec_exec.Coqsum
open Freespec_exec.Coqprod
open Freespec_exec.Coqnum
open Freespec_exec.Coqunit
open Datatypes
open Unix

let try_unix typ to_coq fop =
  to_files_res typ to_coq (try
    Right (fop ())
      with _ -> Left 1)

let files_open = function
    | [coqpath] ->
       let path = string_of_coqbytes coqpath in
       try_unix coqfd_t make_coqfd (fun _ -> openfile path [O_RDONLY] 0o640)
    | _ -> assert false

let files_close = function
    | [coqfd] ->
       let fd = destruct_coqfd coqfd in
       close fd;
       coqtt
    | _ -> assert false

let files_fsize = function
    | [coqfd] ->
       let fd = fd_of_coqfd coqfd in
       try_unix coqint_t int_to_coqint (fun _ -> (fstat fd).st_size)
    | _ -> assert false

let files_read = function
    | [coqfd; coqsize] ->
       let fd = fd_of_coqfd coqfd in
       let size = int_of_coqint coqsize in

       try_unix
         (coqprod_t coqint_t coqbytes_t)
         (prod_to_coqprod coqint_t int_to_coqint coqbytes_t bytes_to_coqbytes)
         (fun _ ->
           let buffer = Bytes.create size in
           let read = read fd buffer 0 size in

           (read, if read < size then Bytes.sub buffer 0 read else buffer))
    | _ -> assert false

let path = "freespec.stdlib.files"

let install_interface =
  register_interface path [
      ("Open", files_open);
      ("Close", files_close);
      ("FSize", files_fsize);
      ("Read", files_read);
    ]

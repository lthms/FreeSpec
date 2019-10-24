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
       let path = string_of_coqstr coqpath in
       try_unix coqfd_t fd_to_coqfd (fun _ -> openfile path [O_RDONLY] 0o640)
    | _ -> assert false

let files_close = function
    | [coqfd] ->
       let fd = fd_of_coqfd coqfd in
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
         (coqprod_t coqint_t coqstr_t)
         (prod_to_coqprod coqint_t int_to_coqint coqstr_t bytes_to_coqstr)
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

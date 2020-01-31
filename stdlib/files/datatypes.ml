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

let fd_to_coqfd fd =
  Coqnum.int_to_coqint (Obj.magic fd)

let fd_of_coqfd coqfd =
  match Constr.kind coqfd with
  | Constr.Int i -> Obj.magic (snd (Uint63.to_int2 i))
  | _ -> assert false

let int_to_files_err x =
  Constr.mkApp (FilesErr.mkConstructor "make_files_err", of_list [int_to_coqint x])

let to_files_res typ to_coq trm =
  sum_to_coqsum FilesErr.mkInductive int_to_files_err typ to_coq trm

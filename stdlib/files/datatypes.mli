val coqfd_t : Constr.constr

val fd_to_coqfd : Unix.file_descr -> Constr.constr
val fd_of_coqfd : Constr.constr -> Unix.file_descr

val int_to_files_err : int -> Constr.constr
val to_files_res : Constr.constr -> ('a -> Constr.constr) -> (int, 'a) Freespec_exec.Coqsum.sum -> Constr.constr


val list_of_coqlist : (Constr.constr -> 'a) ->  Constr.constr -> 'a list
val list_to_coqlist :
  Constr.constr -> ('a -> Constr.constr) -> 'a list -> Constr.constr

val coqlist_iteri : (int -> Constr.constr -> unit) -> Constr.constr -> unit
val coqlist_fold_left : ('a -> Constr.constr -> 'a) -> Constr.constr -> 'a -> 'a

val coqlist_nil : Constr.constr -> Constr.constr
val coqlist_cons : Constr.constr -> Constr.constr -> Constr.constr -> Constr.constr

val coqlist_t : Constr.constr -> Constr.constr


val prod_of_coqprod : (Constr.constr -> 'a) -> (Constr.constr -> 'b) -> Constr.constr -> ('a * 'b)
val prod_to_coqprod :
  Constr.constr -> ('a -> Constr.constr) -> Constr.constr -> ('b -> Constr.constr) -> ('a * 'b) -> Constr.constr

val coqprod_t : Constr.constr -> Constr.constr -> Constr.constr

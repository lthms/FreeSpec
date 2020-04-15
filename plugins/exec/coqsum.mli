type ('a, 'b) sum = Left of 'a | Right of 'b

val sum_of_coqsum : (Constr.constr -> 'a) -> (Constr.constr -> 'b) -> Constr.constr -> ('a, 'b) sum
val sum_to_coqsum : Constr.constr -> ('a -> Constr.constr) -> Constr.constr -> ('b -> Constr.constr) -> ('a, 'b) sum -> Constr.constr

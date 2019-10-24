open Array
open Constr
open Query
open Utils

let prod_of_coqprod of_coq1 of_coq2 prod =
  let (c, args) = app_full prod in
  match (Ind.Prod.constructor_of c, args) with
  | (Some Pair_prod, [_t1; _t2; trm1; trm2])
    -> (of_coq1 trm1, of_coq2 trm2)
  | _
    -> raise (UnsupportedTerm "not a Coq product")

let prod_to_coqprod t1 to_coq1 t2 to_coq2 prod =
  let cPair = Ind.Prod.mkConstructor "pair" in
  match prod with
  | (x, y) ->
     mkApp (cPair, of_list [t1; t2; to_coq1 x; to_coq2 y])

let coqprod_t typ1 typ2 =
  mkApp (Ind.Prod.mkInductive, (of_list [typ1; typ2]))

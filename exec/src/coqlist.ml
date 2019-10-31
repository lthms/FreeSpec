open Array
open Constr
open Query
open Utils

let coqlist_nil typ = mkApp (Ind.List.mkConstructor "nil", of_list [typ])

let coqlist_cons typ trm rstrm = mkApp (Ind.List.mkConstructor "cons", of_list [typ; trm; rstrm])

(* TODO: tailrec version *)
let rec list_of_coqlist of_coq trm =
  let (c, args) = app_full trm in
  match (Ind.List.constructor_of c, args) with
  | (Some Nil_list, [_t]) -> []
  | (Some Cons_list, [_t; coqx; coqrst]) ->
     let x = of_coq coqx in
     let rst = list_of_coqlist of_coq coqrst in
     x :: rst
  | _ -> raise (UnsupportedTerm "of_coqlist: not a Coq list")

(* TODO: tailrec version *)
let rec list_to_coqlist typ to_coq = function
  | [] -> coqlist_nil typ
  | x :: rst ->
     coqlist_cons typ (to_coq x) (list_to_coqlist typ to_coq rst)

let coqlist_t typ =
  mkApp (Ind.List.mkInductive, of_list [typ])

let rec coqlist_fold_left f trm acc =
  let (c, args) = app_full trm in
  match (Ind.List.constructor_of c, args) with
  | (Some Nil_list, [_t]) -> acc
  | (Some Cons_list, [_t; coqx; coqrst]) ->
     coqlist_fold_left f coqrst (f acc coqx)
  | _ -> raise (UnsupportedTerm "coqlist_fold_left: not a Coq list")

let coqlist_iteri f =
  let rec aux idx trm =
    let (c, args) = app_full trm in
    match (Ind.List.constructor_of c, args) with
    | (Some Nil_list, [_t]) -> ()
    | (Some Cons_list, [_t; coqx; coqrst]) ->
       f idx coqx;
       aux (idx + 1) coqrst
    | _ -> raise (UnsupportedTerm "coqlist_iteri: not a Coq list")
  in aux 0

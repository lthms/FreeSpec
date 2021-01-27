(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

open Array
open Constr
open Query
open Utils

let coqlist_nil typ = mkApp (Ind.List.mkConstructor "nil", of_list [typ])

let coqlist_cons typ trm rstrm = mkApp (Ind.List.mkConstructor "cons", of_list [typ; trm; rstrm])

let list_of_coqlist of_coq =
  let rec aux cont trm =
    let (c, args) = app_full trm in
    match (Ind.List.constructor_of c, args) with
    | (Some Nil_list, [_t]) -> cont []
    | (Some Cons_list, [_t; coqx; coqrst]) ->
       let x = of_coq coqx in
       aux (fun next -> cont (x :: next)) coqrst
    | _ -> raise (UnsupportedTerm "of_coqlist: not a Coq list")
  in aux (fun x -> x)

(* TODO: tailrec version *)
let list_to_coqlist typ to_coq =
  let rec aux cont = function
    | [] -> cont (coqlist_nil typ)
    | x :: rst ->
       aux (fun next -> cont (coqlist_cons typ (to_coq x) next)) rst
  in aux (fun x -> x)

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

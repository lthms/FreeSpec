(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

open Array
open Constr
open Query
open Utils

type ('a, 'b) sum = Left of 'a | Right of 'b

let sum_of_coqsum of_coq1 of_coq2 sum =
  let (c, args) = app_full sum in
  match (Ind.Sum.constructor_of c, args) with
  | (Some InL_sum, [_t1; _t2; trm])
    -> Left (of_coq1 trm)
  | (Some InR_sum, [_t1; _t2; trm])
    -> Right (of_coq2 trm)
  | _
    -> raise (UnsupportedTerm "not a Coq sumuct")

let sum_to_coqsum t1 to_coq1 t2 to_coq2 sum =
  let cInR = Ind.Sum.mkConstructor "inr" in
  let cInL = Ind.Sum.mkConstructor "inl" in
  match sum with
  | Left x ->
     mkApp (cInL, of_list [t1; t2; to_coq1 x])
  | Right x ->
     mkApp (cInR, of_list [t1; t2; to_coq2 x])

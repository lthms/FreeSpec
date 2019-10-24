(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2019 Thomas Letan <thomas.letan@ssi.gouv.fr>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>.
 *)

open Query
open Utils
open Constr

(* fold_bits: int -> ('b -> 'c) -> ('b -> bool -> 'b) -> ('b -> 'c) -> 'b -> 'c *)
let fold_bits input fzero fiter flast init =
(* Fold over [input] bits, from the least to the most significant bit, using
   [init] as its initial value:
     - [fzero] is called if [input] is 0
     - [fiter] is called for the least significant bits
     - [flast] is called for the most significant bit *)
  if input == 0
  then fzero init
  else let rec fold_bit_aux input acc =
         let next = input lsr 1 in
         let bit = input land 1 == 1 in
         if next == 0
         then flast acc
         else fold_bit_aux next (fiter acc bit)
       in fold_bit_aux input init

let int_of_coqpositive =
  (* This function does not implement any special protection against integer
     overflow. Because Coq [positive] terms are not bounded, there is no
     guarantee that [int_of_coqpositive] will be equivalent to its argument. *)
  let rec of_coqpositive_aux acc depth p =
    let (p, args) = app_full p in
    match (Ind.Positive.constructor_of p, args) with
    | (Some XH_positive, []) -> acc + depth
    | (Some XO_positive, [next]) -> of_coqpositive_aux acc (2 * depth) next
    | (Some XI_positive, [next]) -> of_coqpositive_aux (acc + depth) (2 * depth) next
    | _ -> raise (UnsupportedTerm "not a constructor of [positive]")
  in of_coqpositive_aux 0 1

let int_to_coqpositive i =
  let cXI = Ind.Positive.mkConstructor "xI" in
  let cXO = Ind.Positive.mkConstructor "xO" in
  let cXH = Ind.Positive.mkConstructor "xH" in
  let not_zero _ =
    raise (UnsupportedTerm "integer is not strictly positive") in
  let fiter cont bit =
    let c = if bit then cXI else cXO in
    fun next -> cont (mkApp (c, (Array.of_list [next]))) in
  let flast cont = cont cXH in
  fold_bits i not_zero fiter flast (fun x -> x)

let int_of_coqz z =
  let (z, args) = app_full z in
  match (Ind.Z.constructor_of z, args) with
  | (Some Z0_Z, []) -> 0
  | (Some Zpos_Z, [p]) -> int_of_coqpositive p
  | (Some Zneg_Z, [p]) -> -1 * int_of_coqpositive p
  | _ -> raise (UnsupportedTerm "not a constructor of [Z]")

let int_to_coqz = function
  | x when x > 0 -> mkApp (Ind.Z.mkConstructor "Zpos", Array.of_list [int_to_coqpositive x])
  | 0 -> Ind.Z.mkConstructor "Z0"
  | x -> mkApp (Ind.Z.mkConstructor "Zneg", Array.of_list [int_to_coqpositive (-1 * x)])

let int_of_coqint coqint =
  match Constr.kind coqint with
  | Constr.Int i -> snd (Uint63.to_int2 i)
  | _ -> raise (UnsupportedTerm "Not a native integer")

let int_to_coqint v =
  Constr.(of_kind (Int (Uint63.of_int v)))

let coqint_t =
  match Coqlib.lib_ref "num.int63.type" with
  | Globnames.ConstRef c -> Constr.mkConst c
  | _ -> raise (Utils.Anomaly "Could not construct the type int")

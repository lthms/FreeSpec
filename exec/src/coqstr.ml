(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *

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

let char_of_ascii ascii =
  let (c, args) = app_full ascii in
  match kind c with
  | Construct _ (* this should be bool *)
    -> let coqbool_to_int = fun acc x ->
         match kind x with
         | Construct (c, _) ->
            (match Ind.Bool.constructor_of c with
             | Some x -> 2 * acc + if x then 1 else 0
             | _ -> raise (UnsupportedTerm "not a [bool] constructor"))
         | _ -> raise (UnsupportedTerm "Axiomatic [bool]")
       in
       char_of_int (List.fold_left coqbool_to_int 0 (List.rev args))
  | _
    -> raise (UnsupportedTerm "Trying to use an axiomatic [ascii]")

let char_to_ascii char =
  let src = int_of_char char in
  let cTrue = Ind.Bool.mkConstructor "true" in
  let cFalse = Ind.Bool.mkConstructor "false" in
  let cAscii = Ind.Ascii.mkConstructor "Ascii" in
  let coqbool_of_bool b = if b then cTrue else cFalse in
  let rec int_to_bool_l depth x acc =
    if depth != 0
    then int_to_bool_l (depth-1) (x/2) ((if x mod 2 == 1 then true else false) :: acc)
    else acc in
  let l = List.rev (int_to_bool_l 8 src []) in
  mkApp (cAscii, Array.of_list (List.map coqbool_of_bool l))

let rec print_lchar = function
  | x :: rst -> print_char x; print_lchar rst
  | [] -> ()

let rec lchar_of_coqstr coq_str =
  let (c, args) = app_full coq_str in
  match kind c with
  | Construct (c, _)
    -> (match (Ind.String.constructor_of c, args) with
        | (Some EmptyString_string, []) -> []
        | (Some String_string, [ascii; rst])
          -> char_of_ascii ascii :: lchar_of_coqstr rst
        | _ -> raise (Anomaly "Unknown [string] constructor"))
  | _
    -> raise (UnsupportedTerm "Trying to print an axiomatic [string]")

let rec str_of_lchar = function
  | x :: rst -> String.make 1 x ^ str_of_lchar rst
  | _ -> ""

let rec coqstr_of_lchar = function
  | x :: rst
    -> let x = char_to_ascii x in
       let rst = coqstr_of_lchar rst in
       mkApp (Ind.String.mkConstructor "String", Array.of_list [x; rst])
  | _ -> Ind.String.mkConstructor "EmptyString"

let lchar_of_str s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in exp (String.length s - 1) []

let coqstr_of_str s = coqstr_of_lchar (lchar_of_str s)
let str_of_coqstr s = str_of_lchar (lchar_of_coqstr s)

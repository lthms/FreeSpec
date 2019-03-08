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

open Array
open Constr
open Query
open Utils

let char_of_coqascii ascii =
  let (c, args) = app_full ascii in
  match kind c with
  | Construct _ (* this should be ascii *)
    -> let of_coqascii_aux = fun acc x ->
         2 * acc + if (Coqbool.bool_of_coqbool x) then 1 else 0
       in
       char_of_int (List.fold_left of_coqascii_aux 0 (List.rev args))
  | _
    -> raise (UnsupportedTerm "Trying to use an axiomatic [ascii]")

let char_to_coqascii char =
  let src = int_of_char char in
  let cAscii = Ind.Ascii.mkConstructor "Ascii" in
  let rec int_to_booll depth x acc =
    if depth != 0
    then int_to_booll (depth-1) (x/2) (Coqbool.bool_to_coqbool (x mod 2 == 1)::acc)
    else acc
  in
  mkApp (cAscii, of_list @@ List.rev (int_to_booll 8 src []))

(* val bytes_fold_chars: bytes -> ('b -> char -> 'b) -> 'b -> 'b *)
let bytes_fold_chars_rev str f =
  let rec aux i acc =
    if 0 <= i then aux (i-1) (f acc @@ Bytes.get str i) else acc
  in aux (Bytes.length str - 1)

(* val coqstr_fold_chars: Constr.constr -> ('b -> char -> 'b) -> 'b -> 'b *)
let coqstr_fold_chars coqstr f =
  let rec aux coqstr acc =
    let (c, args) = app_full coqstr in
      match (Ind.String.constructor_of c, args) with
      | (Some EmptyString_string, []) -> acc
      | (Some String_string, [ascii; rst])
        -> aux rst (f acc (char_of_coqascii ascii))
      | _ -> raise (Anomaly "Unknown [string] constructor")
  in aux coqstr

let bytes_to_coqstr str =
  let cString = Ind.String.mkConstructor "String" in
  let cEmpty = Ind.String.mkConstructor "EmptyString" in
  let aux acc c = mkApp (cString, of_list [char_to_coqascii c; acc]) in
  bytes_fold_chars_rev str aux cEmpty

let bytes_of_coqstr coqstr =
  let size = coqstr_fold_chars coqstr (fun x _ -> x + 1) 0 in
  let buffer = Bytes.create size in
  let aux idx c =
    let _ = Bytes.set buffer idx c in
    idx + 1
  in
  let _ = coqstr_fold_chars coqstr aux 0 in
  buffer

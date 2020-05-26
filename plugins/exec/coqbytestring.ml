(* FreeSpec
 * Copyright (C) 2018–2020 ANSSI
 *
 * Contributors:
 * 2020 Thomas Letan <thomas.letan@ssi.gouv.fr>
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

open Coqbase
open Constr
open Query
open Coqbyte
open Utils

let coqbytestr_nil = Ind.Bytestring.mkConstructor "bytes_nil"
let coqbytestr_cons x rst =
  mkApp
    (Ind.Bytestring.mkConstructor "bytes_cons", Array.of_list [rst])

let rec coqbytestr_fold_left f trm acc =
  let (c, args) = app_full trm in
  match (Ind.Bytestring.constructor_of c, args) with
  | (Some Bytes_nil, []) -> acc
  | (Some Bytes_cons, [coqx; coqrst]) ->
     coqbytestr_fold_left f coqrst (f acc coqx)
  | _ -> raise (UnsupportedTerm "coqbytestr_fold_left: not a bytestring")

let coqbytestr_iteri f =
  let rec aux idx trm =
    let (c, args) = app_full trm in
    match (Ind.Bytestring.constructor_of c, args) with
    | (Some Bytes_nil, []) -> ()
    | (Some Bytes_cons, [coqx; coqrst]) ->
       f idx coqx;
       aux (idx + 1) coqrst
    | _ -> raise (UnsupportedTerm "coqbytestr_iteri: not a bytestring")
  in aux 0

let bytestring_of_coqbytestring trm =
  let size = coqbytestr_fold_left (fun x _ -> x + 1) trm 0 in
  let buffer = Bytes.create size in
  let aux idx c = Bytes.set buffer idx (char_of_coqbyte c) in
  let _ = coqbytestr_iteri aux trm in
  Bytestring.of_string (Bytes.to_string buffer)

let bytestring_to_coqbytestring b =
  Seq.fold_left
    (fun cont c next -> cont (coqbytestr_cons (char_to_coqbyte c) next))
    (fun x -> x)
    (String.to_seq (Bytestring.to_string b))
    coqbytestr_nil

let coqbytestring_t = Ind.Bytestring.mkInductive

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

open Extends
open Coqnum
open Coqunit

type 'a stream = Cons of ('a * (unit -> 'a stream))

let rec from n = Cons (n, fun _ -> from (n + 1))

let keys = ref (from 0)

let fresh_key _ =
  match !keys with
  | Cons (n, next) -> begin
      keys := next ();
      n
    end

let free_key k =
  keys := Cons (k, fun _ -> !keys)

let heap : (int, Constr.t) Hashtbl.t =
  Hashtbl.create ~random:false 100

let new_ref trm = begin
  let k = fresh_key () in
  Hashtbl.add heap k trm;
  k
end

let destruct k = begin
  Hashtbl.remove heap k;
  free_key k
end

let assign = Hashtbl.replace heap

let deref = Hashtbl.find heap

(* private *)

let path = "freespec.exec.heap"

let _ =
  let new_ref_primitive = function
    | [_term_type; trm]
      -> int_to_coqint @@ new_ref trm
    | _ -> assert false in
  let assign_primitive = function
    | [_term_type; ptr; trm]
      -> begin
          assign (int_of_coqint ptr) trm;
          coqtt
        end
    | _ -> assert false in
  let deref_primitive = function
    | [_term_type; ptr]
      -> deref (int_of_coqint ptr)
    | _ -> assert false in
  let destruct_primitive = function
    | [_term_type; ptr]
      -> begin
          destruct (int_of_coqint ptr);
          coqtt
        end
    | _ -> assert false in
  register_interface path [
    ("NewRef", new_ref_primitive);
    ("Assign", assign_primitive);
    ("Deref", deref_primitive);
    ("Destruct", destruct_primitive);
  ]

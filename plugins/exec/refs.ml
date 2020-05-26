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
open Coqunit

let heap = Store.create ()
let new_ref = Store.add heap
let destruct = Store.remove heap
let assign = Store.replace heap
let deref = Store.find heap

(* private *)

let path = "freespec.exec.heap"

let _ =
  let new_ref_primitive = function
    | [_term_type; trm]
      -> new_ref trm
    | _ -> assert false in
  let assign_primitive = function
    | [_term_type; ptr; trm]
      -> begin
          assign ptr trm;
          coqtt
        end
    | _ -> assert false in
  let deref_primitive = function
    | [_term_type; ptr]
      -> deref ptr
    | _ -> assert false in
  let destruct_primitive = function
    | [_term_type; ptr]
      -> begin
          destruct ptr;
          coqtt
        end
    | _ -> assert false in
  register_interface path [
    ("NewRef", new_ref_primitive);
    ("Assign", assign_primitive);
    ("Deref", deref_primitive);
    ("Destruct", destruct_primitive);
  ]

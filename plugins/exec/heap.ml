(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

open Extends
open Coqunit
open Coqi63

let count = ref 0

let heap : (int, Constr.t) Hashtbl.t =
  Hashtbl.create ~random:false 100

let make_ref trm = begin
  let k = !count in
  count := !count + 1;
  Hashtbl.add heap k trm;
  int_to_coqint k
end

let destruct k = begin
  Hashtbl.remove heap (int_of_coqint k);
end

let assign k = Hashtbl.replace heap (int_of_coqint k)

let deref k = Hashtbl.find heap (int_of_coqint k)

(* private *)

let path = "freespec.ffi.REFS"

let _ =
  let new_ref_primitive = function
    | [_term_type; trm]
      -> make_ref trm
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
  register_interface path [
    ("Make_ref", new_ref_primitive);
    ("Assign", assign_primitive);
    ("Deref", deref_primitive);
  ]

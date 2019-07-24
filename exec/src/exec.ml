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

open Constr
open Query
open Utils
open Interfaces

let reduce_all env evm trm =
  EConstr.to_constr evm (Reductionops.nf_all env evm (EConstr.of_constr trm))

let exec_request instr_t instr_trm func_trm =
  let rec find_primitive instr_trm =
    let (instr_trm, args) = app_full instr_trm in
    match (kind instr_trm, args) with
    | (Construct (c, _), args)
      -> (match (Ind.IPlus.constructor_of instr_trm, args) with
          | (Some _, [_; _; _; trm])
            -> find_primitive trm
          | _
            -> (c, args))
    | (Case _, [_; trm]) | (LetIn _, [_; trm])
      -> find_primitive trm
    | _
      -> raise (UnsupportedTerm "Unsupported primitive shape")
  in
  let (c, args) = find_primitive instr_trm in
  (* [primitive_semantic] may raise [UnsupportedInterface] if [c] is not a
     registered request constructors.  *)
  let res = primitive_semantic c args in
  mkApp (func_trm, Array.of_list [res])

let rec exec env evm def =
  Interfaces.force_interface_initializers ();
  let def = Reduction.whd_all env def in
  let (def, args) = app_full def in
  match (Ind.Program.constructor_of def, args) with
  | (Some RequestThen_impure,
     [instr_t; _ret_t; _instr_ret_t; instr_trm; func_trm])
    -> let instr_trm = reduce_all env evm instr_trm in
       exec env evm (exec_request instr_t instr_trm func_trm)
  | (Some Local_impure, _)
    -> ()
  | _
    -> raise (UnsupportedTerm "FreeSpe.Exec only handles [FreeSpec.Program] terms.")

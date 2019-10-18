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
open Attributes
open Attributes.Notations

let reduce_head env evm trm =
  EConstr.to_constr evm (Reductionops.whd_all env evm (EConstr.of_constr trm))

let reduce_all env evm trm =
  EConstr.to_constr evm (Reductionops.nf_all env evm (EConstr.of_constr trm))

let reduce_strategy =
  bool_attribute ~name:"Reduce Strategy" ~on:"nf" ~off:"whd" >>=
    function
    | Some true -> return reduce_all
    | _ -> return reduce_head

let exec_request instr_trm func_trm =
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

let rec exec head_red env evm def =
  let def = head_red env evm def in
  let (def, args) = app_full def in
  match Ind.Program.constructor_of def with
  | Some RequestThen_impure ->
     begin match args with
     | [_instr_t; _ret_t; _instr_ret_t; instr_trm; func_trm] ->
        let instr_trm = reduce_all env evm instr_trm in
        exec head_red env evm (exec_request instr_trm func_trm)
     | _ -> assert false
     end
  | Some Local_impure
    -> None
  | _
    -> raise (UnsupportedTerm "FreeSpe.Exec only handles [FreeSpec.Program] terms.")

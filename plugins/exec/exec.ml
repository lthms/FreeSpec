(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

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

let exec_request env evm instr_trm func_trm =
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
      -> raise (UnsupportedTerm
                  ("Unsupported primitive shape `"
                   ^ (Pp.string_of_ppcmds @@ Printer.pr_lconstr_env env evm instr_trm)
                   ^ "'"))
  in
  let (c, args) = find_primitive instr_trm in
  (* [primitive_semantic] may raise [UnsupportedInterface] if [c] is not a
     registered request constructors.  *)
  try
    let res = primitive_semantic c args in
    mkApp (func_trm, Array.of_list [res])
  with UnsupportedInterface ->
    raise (UnsupportedTerm
             ("No semantics has been installed for primitive `"
              ^ (Pp.string_of_ppcmds @@ Printer.pr_lconstr_env env evm instr_trm)
              ^ "'"))

let rec exec head_red env evm def =
  let def = head_red env evm def in
  let (def, args) = app_full def in
  match Ind.Program.constructor_of def with
  | Some RequestThen_impure ->
     begin match args with
     | [_instr_t; _ret_t; _instr_ret_t; instr_trm; func_trm] ->
        let instr_trm = reduce_all env evm instr_trm in
        exec head_red env evm (exec_request env evm instr_trm func_trm)
     | _ -> assert false
     end
  | Some Local_impure
    -> None
  | _
    -> raise (UnsupportedTerm
                ("FreeSpec.Exec cannot handle the term `"
                 ^ (Pp.string_of_ppcmds @@ Printer.pr_lconstr_env env evm def)
                 ^ "'"))

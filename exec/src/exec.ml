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
open Coqstr

let reduce_all env evm trm =
  EConstr.to_constr evm (Reductionops.nf_all env evm (EConstr.of_constr trm))

let exec_request instr_t instr_trm func_trm =
  match kind instr_t with
  | Ind (i, _)
    -> if Ind.ConsoleI.ref_is i
       then let (instr_trm, args) = app_full instr_trm in
            (match kind instr_trm with
             | Construct (c, _)
               -> let res =
                    match (Ind.ConsoleI.constructor_of c, args) with
                    | (Some Scan_console, [])
                      -> coqstr_of_str (Console.scan ())
                    | (Some Echo_console, [str])
                      -> Console.echo (str_of_coqstr str);
                         Ind.Unit.mkConstructor "tt"
                    | _
                      -> raise (Anomaly "Unknown [Console.i] constructor")
                  in mkApp (func_trm, Array.of_list [res])
             | _ -> raise (UnsupportedTerm "Trying to execute an axiomatic [Console.i]"))
       else raise UnsupportedInterface
  | _ -> raise UnsupportedInterface

let rec exec env evm def =
  let def = Reduction.whd_all env def in
  let (def, args) = app_full def in
  match kind def with
  | Construct (c, _)
    -> (match (Ind.Program.constructor_of c, args) with
        | (Some Request_program, [instr_t; _ret_t; _instr_ret_t; instr_trm; func_trm])
          -> let instr_trm = reduce_all env evm instr_trm in
             exec env evm (exec_request instr_t instr_trm func_trm)
        | (Some Pure_program, _)
          -> ()
        | _
          -> raise (UnsupportedTerm "coq-exec only execute [Program] terms."))
  | _
    -> raise (UnsupportedTerm "It was not possible to reduce your term.")

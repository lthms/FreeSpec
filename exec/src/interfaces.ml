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

open Query
open Utils
open Coqstr

type effectful_semantic = Constr.constr list -> Constr.constr

let primitive_semantics = ref Names.Constrmap.empty

let new_primitive m c p =
  let m = exec_instr_pkg m in
  match Coqlib.gen_reference_in_modules contrib [m] c with
    | Names.GlobRef.ConstructRef c ->
       primitive_semantics := Names.Constrmap.add c p !primitive_semantics
    | _ ->
       invalid_arg "Only constructor can identify primitives."

let primitive_semantic : Names.constructor -> effectful_semantic =
  fun c -> try
    Names.Constrmap.find c !primitive_semantics
  with Not_found -> raise UnsupportedInterface

let install_interfaces = lazy (
  new_primitive "Console" "Scan" (function [] ->
    coqstr_of_str (Console.scan ())
  | _ -> assert false);

  new_primitive "Console" "Echo" (function [str] ->
    Console.echo (str_of_coqstr str);
    Ind.Unit.mkConstructor "tt"
  | _ -> assert false)
)

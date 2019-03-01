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

(**

   The OCaml interpretation of an effectful primitive is an
   effectful OCaml function from Coq terms to Coq term.

*)
type effectful_semantic = Constr.constr list -> Constr.constr

let primitive_semantics : effectful_semantic Names.Constrmap.t ref =
  ref Names.Constrmap.empty

let new_primitive m c p =
  match Coqlib.gen_reference_in_modules contrib [m] c with
    | Names.GlobRef.ConstructRef c ->
       primitive_semantics := Names.Constrmap.add c p !primitive_semantics
    | _ ->
       invalid_arg "Only constructor can identify primitives."

let primitive_semantic : Names.constructor -> effectful_semantic =
  fun c -> try
    Names.Constrmap.find c !primitive_semantics
  with Not_found -> raise UnsupportedInterface

let initializers = Queue.create ()

let register_interfaces interface_initializer =
  Queue.add interface_initializer initializers

let force_interface_registering () =
  Queue.(
    while not (is_empty initializers) do
      pop initializers ()
    done
  )

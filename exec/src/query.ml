(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
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

let contrib = "exec"
let exec_instr_pkg istr = ["FreeSpec"; "Exec"; "Interfaces"; istr]

module type InductiveSpec = sig
  type constructor
  val type_name : string
  val names : (string * constructor) list
  val modlist : string list
end

module Inductive = struct
  module Make (I: InductiveSpec) = struct
    let constructor_of c =
      let constructor_is = fun cstr ->
        Names.GlobRef.equal
          (Globnames.ConstructRef c)
          (Coqlib.gen_reference_in_modules contrib [I.modlist] cstr)
      in
      let rec aux = function
        | (str, descr) :: rst
          -> if constructor_is str
             then Some descr
             else aux rst
        | _ -> None
      in aux I.names

    let mkConstructor cstr =
      let ref = Coqlib.gen_reference_in_modules contrib [I.modlist] cstr in
      match ref with
      | Globnames.ConstructRef c -> Constr.mkConstruct c
      | _ -> raise (Utils.Anomaly "Could not construct the term")

    let ref_is i =
      Names.GlobRef.equal
        (Globnames.IndRef i)
        (Coqlib.gen_reference_in_modules contrib [I.modlist] I.type_name)

  end
end

type program_constructor = Pure_program | Request_program
type console_constructor = Scan_console | Echo_console
type string_constructor = EmptyString_string | String_string
type ascii_constructor = Ascii_ascii

module Ind = struct
  module Program =
    Inductive.Make(struct
        type constructor = program_constructor
        let type_name = "Program"
        let modlist = ["FreeSpec"; "Program"]
        let names = [("Pure", Pure_program); ("Request", Request_program)]
      end)

  module ConsoleI =
    Inductive.Make(struct
        type constructor = console_constructor
        let type_name = "i"
        let modlist = exec_instr_pkg "Console"
        let names = [("Scan", Scan_console); ("Echo", Echo_console)]
      end)

  module String =
    Inductive.Make(struct
        type constructor = string_constructor
        let type_name = "string"
        let modlist = ["Coq"; "Strings"; "String"]
        let names = [("EmptyString", EmptyString_string); ("String", String_string)]
      end)

  module Ascii =
    Inductive.Make(struct
        type constructor = ascii_constructor
        let type_name = "ascii"
        let modlist = ["Coq"; "Strings"; "Ascii"]
        let names = [("Ascii", Ascii_ascii)]
      end)

  module Bool =
    Inductive.Make(struct
        type constructor = bool
        let type_name = "bool"
        let modlist = ["Coq"; "Init"; "Datatypes"]
        let names = [("true", true); ("false", false)]
      end)

  module Unit =
    Inductive.Make(struct
        type constructor = unit
        let type_name = "unit"
        let modlist = ["Coq"; "Init"; "Datatypes"]
        let names = [("tt", ())]
      end)
end

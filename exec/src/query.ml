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

let contrib = "exec"

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
        match Constr.kind c with
        | Constr.Construct (c, _)
          -> Names.GlobRef.equal
               (Globnames.ConstructRef c)
               (Coqlib.gen_reference_in_modules contrib [I.modlist] cstr)
        | _ -> false
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
      match Constr.kind i with
      | Constr.Ind (i, _)
        -> Names.GlobRef.equal
             (Globnames.IndRef i)
             (Coqlib.gen_reference_in_modules contrib [I.modlist] I.type_name)
      | _ -> false

  end
end

type program_constructor = Pure_program | Request_program
type intcompose_constructor = InL_intcompose | InR_intcompose
type string_constructor = EmptyString_string | String_string
type ascii_constructor = Ascii_ascii
type positive_constructor = XI_positive | XO_positive | XH_positive
type z_constructor = Z0_Z | Zpos_Z | Zneg_Z

module Ind = struct
  module Program =
    Inductive.Make(struct
        type constructor = program_constructor
        let type_name = "Program"
        let modlist = ["FreeSpec"; "Program"]
        let names = [("Pure", Pure_program); ("Request", Request_program)]
      end)

  module IntCompose =
    Inductive.Make(struct
        type constructor = intcompose_constructor
        let type_name = "IntCompose"
        let modlist = ["FreeSpec"; "Compose"]
        let names = [("InL", InL_intcompose); ("InR", InR_intcompose)]
      end)

  module Positive =
    Inductive.Make(struct
        type constructor = positive_constructor
        let type_name = "positive"
        let modlist = ["Coq"; "Numbers"; "BinNums"]
        let names = [("xI", XI_positive); ("xO", XO_positive); ("xH", XH_positive)]
      end)

  module Z =
    Inductive.Make(struct
        type constructor = z_constructor
        let type_name = "Z"
        let modlist = ["Coq"; "Numbers"; "BinNums"]
        let names = [("Z0", Z0_Z); ("Zpos", Zpos_Z); ("Zneg", Zneg_Z)]
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

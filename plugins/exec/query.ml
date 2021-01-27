(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

let contrib = "exec"

module type InductiveSpec = sig
  type constructor
  val type_name : string
  val names : (string * constructor) list
  val namespace : string
end

module Inductive = struct
  module Make (I: InductiveSpec) = struct
    let constructor_of c =
      let constructor_is = fun cstr ->
        match Constr.kind c with
        | Constr.Construct (c, _)
          -> Names.GlobRef.equal
               (Names.GlobRef.ConstructRef c)
               (Coqlib.lib_ref (I.namespace ^ "." ^ cstr))
        | _ -> false
      in
      let rec aux = function
        | (str, descr) :: rst
          -> if constructor_is str
             then Some descr
             else aux rst
        | _ -> None
      in aux I.names

    let mkInductive =
      let ref = Coqlib.lib_ref (I.namespace ^ ".type") in
      match ref with
      | Names.GlobRef.IndRef i -> Constr.mkInd i
      | _ -> raise (Utils.Anomaly "Could not construct inductive type")

    let mkConstructor cstr =
      let ref = Coqlib.lib_ref (I.namespace ^ "." ^ cstr) in
      match ref with
      | Names.GlobRef.ConstructRef c -> Constr.mkConstruct c
      | _ -> raise (Utils.Anomaly "Could not construct the term")

    let ref_is i =
      match Constr.kind i with
      | Constr.Ind (i, _)
        -> Names.GlobRef.equal
             (Names.GlobRef.IndRef i)
             (Coqlib.lib_ref (I.namespace ^ ".type"))
      | _ -> false

  end
end

type impure_constructor = Local_impure | RequestThen_impure
type iplus_constructor = InL_intcompose | InR_intcompose
type prod_constructor = Pair_prod
type sum_constructor = InL_sum | InR_sum
type list_constructor = Cons_list | Nil_list
type i63_constructor = Mk_i63 | Nil_list

module Ind = struct
  module Program =
    Inductive.Make(struct
        type constructor = impure_constructor
        let type_name = "impure"
        let namespace = "freespec.core.impure"
        let names = [("local", Local_impure); ("request_then", RequestThen_impure)]
      end)

  module IPlus =
    Inductive.Make(struct
        type constructor = iplus_constructor
        let type_name = "iplus"
        let namespace = "freespec.core.iplus"
        let names = [("in_left", InL_intcompose); ("in_right", InR_intcompose)]
      end)

  module Bool =
    Inductive.Make(struct
        type constructor = bool
        let type_name = "bool"
        let namespace = "core.bool"
        let names = [("true", true); ("false", false)]
      end)

  module Unit =
    Inductive.Make(struct
        type constructor = unit
        let type_name = "unit"
        let namespace = "core.unit"
        let names = [("tt", ())]
      end)

  module Prod =
    Inductive.Make(struct
        type constructor = prod_constructor
        let type_name = "prod"
        let namespace = "core.prod"
        let names = [("pair", Pair_prod)]
      end)

  module Sum =
    Inductive.Make(struct
        type constructor = sum_constructor
        let type_name = "sum"
        let namespace = "core.sum"
        let names = [("inl", InL_sum); ("inr", InR_sum)]
      end)

  module List =
    Inductive.Make(struct
        type constructor = list_constructor
        let type_name = "list"
        let namespace = "core.list"
        let names = [("cons", Cons_list); ("nil", Nil_list)]
      end)

  module Byte =
    Inductive.Make(struct
        type constructor = unit
        let type_name = "byte"
        let namespace = "coq.byte"
        let names = []
      end)

  module I63 =
    Inductive.Make(struct
        type constructor = i63_constructor
        let type_name = "i63"
        let namespace = "coqffi.data.i63"
        let names = [("mk_i63", Mk_i63)]
      end)
end

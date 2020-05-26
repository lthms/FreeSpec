open Constr
open Query
open Utils

let char_of_coqbyte trm =
  match kind trm with
  | Construct ((_, x), _) -> Char.chr (x - 1) (* constructor indexes start at 1 *)
  | _ -> raise (UnsupportedTerm "not a Byte")

let char_to_coqbyte c =
  match kind Ind.Byte.mkInductive with
  | Ind (i, _) -> Constr.mkConstruct (i, 1 + Char.code c)
  | _ -> assert false

let coqbyte_t = Ind.Byte.mkInductive

open Format

(* We arbitrarily fix a upper bound for the number of generated
   [ProvideN] and [StrictProvideN] typeclasses.  Ideally, we would
   like to come up with a setup where this is no longer needed, e.g.,
   with a typeclass hierarchy that could scale with any number of
   interfaces, but we failed to come up with a satisfying alternative.
   There is nothing that prevent us from incrementing this value if
   there is a good use cas that needs it, but the greater the constant
   is, the longer it takes to compile the generated file. *)
let max_interfaces = 15

(** [x -- y] computes [[x; x+1; ...; y-1; y]] *)
let rec ( -- ) x y = if x < y then x :: (x + 1 -- y) else [ y ]

(** [x --- y] computes [[(x,x+1); ...; (x,y-1); (x,y); (x+1; x+2);
    ... (y-1, y)]] *)
let ( --- ) x y =
  let ln = x -- y in
  let rec row x = function
    | y :: rst when x <> y -> (x, y) :: row x rst
    | _ :: rst -> row x rst
    | [] -> []
  in
  List.concat_map (fun x -> row x ln) ln

let prelude = "From FreeSpec.Core Require Import Interface."

let pp_interfaces =
  pp_print_list
    ~pp_sep:(fun fmt () -> pp_print_string fmt " ")
    (fun fmt i -> fprintf fmt "i%d" i)

let pp_provide_args =
  pp_print_list
    ~pp_sep:(fun fmt () -> pp_print_string fmt ", ")
    (fun fmt i -> fprintf fmt "Provide ix i%d" i)

let pp_provide_n fmt n =
  fprintf fmt
    "Class Provide%d ix %a `{%a}.@ @ #[global] Hint Resolve Build_Provide%d : \
     typeclass_instances."
    n pp_interfaces (1 -- n) pp_provide_args (1 -- n) n

let pp_distinguish_args =
  pp_print_list
    ~pp_sep:(fun fmt () -> pp_print_string fmt ", ")
    (fun fmt (x, y) -> fprintf fmt "! Distinguish ix i%d i%d" x y)

let pp_strict_provide_n fmt n =
  fprintf fmt
    "Class StrictProvide%d ix %a `{%a, %a}.@ @ #[global] Hint Resolve \
     Build_StrictProvide%d : typeclass_instances."
    n pp_interfaces (1 -- n) pp_provide_args (1 -- n) pp_distinguish_args
    (1 --- n) n

let () =
  printf "@[<v>";
  printf "%s@ @ " prelude;
  printf "%a@ @ "
    (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@ @ ") pp_provide_n)
    (1 -- max_interfaces);
  printf "%a"
    (pp_print_list
       ~pp_sep:(fun fmt () -> fprintf fmt "@ @ ")
       pp_strict_provide_n)
    (2 -- max_interfaces);
  printf "@]"

From FreeSpec.Core Require Import All.

Extraction Inline impure_Applicative.

Class HasMLImpl ix :=
  { ml_semantics : semantics ix }.

Instance ExtractiblePlus `(HasMLImpl i, HasMLImpl j)
  : HasMLImpl (i + j) :=
  { ml_semantics := ml_semantics * ml_semantics }.

Definition gen_main {α} `{HasMLImpl ix} : impure ix α -> α :=
  eval_impure ml_semantics.

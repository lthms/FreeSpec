(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2021 Nomadic Labs *)

From FreeSpec.Core Require Import Core CoreFacts.
From FreeSpec.Contribs Require Import Raise MFix.

Fixpoint mfix_with_gas `{Provide2 ix MFIX (RAISE t)}
   `(rec : (t -> impure ix u) -> t -> impure ix u) (gas : nat) (x : t)
  : impure ix u :=
  match gas with
  | O => raise x
  | S n => rec (mfix_with_gas rec n) x
  end.

(*
Axiom mfix_pre
  : forall `{MayProvide ix i, StrictProvide2 ix MFIX (RAISE t),
             ! Distinguish ix (RAISE t) i, ! Distinguish ix MFIX i}
           `(c : contract i Ω)
           `(rec : (t -> impure ix u) -> t -> impure ix u) (ω : Ω) (x : t),
    pre (to_hoare c (mfix rec x)) ω
    <-> forall gas, pre (to_hoare c (mfix_with_gas rec gas x)) ω.

Axiom mfix_post
  : forall `{MayProvide ix i, StrictProvide2 ix MFIX (RAISE t),
             ! Distinguish ix (RAISE t) i, ! Distinguish ix MFIX i}
           `(c : contract i Ω)
           `(rec : (t -> impure ix u) -> t -> impure ix u) (ω ω' : Ω)
            (x : t) (r : u),
    post (to_hoare c (mfix rec x)) ω r ω'
    <-> exists gas, post (to_hoare c (mfix_with_gas rec gas x)) ω r ω'.
*)

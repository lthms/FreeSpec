(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2021 Nomadic Labs *)

From ExtLib Require Import MonadFix Monad.
From FreeSpec.Core Require Import Impure.
From FreeSpec.Contribs Require Import Raise.
Import MonadLetNotation.

(** Diverging computations are an open problem in FreeSpec since the
    beginning, due to the use of an inductive datatype to define
    [impure].  

    Turning [impure] into a coinductive type could be achieved, but it
    would mean [run_impure] would have to compute the trace of an
    execution rather than its result.

    Another approach is to consider the act of diverging is an effect
    that we can encode as an effect.  Regardless of its feasability,
    this approach has the nice benefit to force developers to “mark”
    their diverging functions as such.

    Diverging as an effect is not a novel idea.  It is usually encoded
    by the [mfix] monadic operator, whose type is:

<<
mfix : ((t -> m u) -> t -> m u) -> t -> m u
>>

    In FreeSpec, [mfix] can be encoded as follows:
  
<<
Inductive MFIX (i : interface) : interface :=
| MFix {t u} (rec : (t -> impure i u) -> t -> impure i u) (x : t) : MFIX i u.
  
Arguments MFix [i t u].
>>
  
    Here we see [MFIX] is not like the [interface] types we have
    previously defined in FreeSpec, in that its primitive takes an
    [impure] function as one of its arguments.  As a consequence,
    [MFIX] needs to be parameterized by an interface itself, making it
    a “higher-order interface.”
  
    This poses many challenges. For instance, how should we define
    [mfix] (the helper to use [MFix])? 
  
    There most natural candidate is
  
<<
  Definition mfix `{Provide ix (MFIX ix')} {u t}
      (rec : (t -> impure ix' u) -> t -> impure ix' u) (x : t)
    : impure ix u :=
    request (MFix rec x).
>>
  
    As far as we can tell as of now, does not “break” the reasoning
    framework of FreeSpec… Meaning you should be able to use the
    reasoning framework of FreeSpec.  Unfortunately, un practice it is
    really counter-intuitive to use.
  
    Can you infer the behavior of the following program?
  
<<
Definition inc_nth
   `{Provide ix (MFIX ix'), Provide ix (STORE nat), Provide ix' (STORE nat)}
    (n : nat)
  : impure ix nat :=
  put 0%nat;; (* (1) *)
  mfix (fun rec _ =>
          let* count := get in (* (2) *)
          if (Nat.eqb count n)%nat
          then local n
          else put (count + 1)%nat;; rec tt) tt.
>>
  
    Because [ix] and [ix'] are two separate interfaces, the effect of
    [put 0] (see (1)) is not correlated to the effect of [get] (see
    (2)).
  
    That is, we need [ix] and [ix'] to be the same interface, for the
    effect of the [STORE] to be correlated.  We can specify it by
    defining only one interface.
  
<<
Definition inc_nth'
   `{Provide ix (MFIX ix), Provide ix (STORE nat)}
    (n : nat)
  : impure ix nat :=
  put 0%nat;; (* (1) *)
  mfix (fun rec _ =>
          let* count := get in (* (2) *)
          if (Nat.eqb count n)%nat
          then local n
          else put (count + 1)%nat;; rec tt) tt.
>>

    There are many problems with this definition, though.  Firstly, we
    are not sure such a [ix] exists, and we know better than to reason
    with empty types.  Secondly, this breaks the main assumption upon
    which FreeSpec reasoning framework is built: interfaces are
    independent from each other.  A call of [STORE] primitives cannot
    alter the semantics of [MFIX]… but somehow, a call to [MFix] can
    alter the semantics of [STORE].  FreeSpec is not equiped to deal
    with this setting.

    Interfaces are a rendez-vous point for two software components.
    Diverging is a local behavior, one which cannot be observed by
    another.  As a consequence, implementing this effect as a
    constructor of an interface feels forced.

    However, we like the idea of marking a function to advertize its
    potentially diverging behavior.  To that end, we introduce an
    axiomatized [LOOP] interface. *)

Axiom MFIX : interface.

(** But this time, rather than defining [mfix] as a primitive, we
    axiomatized it. *)

Axiom mfix
  : forall `{Provide ix MFIX} {t u},
    ((t -> impure ix u) -> t -> impure ix u) -> t -> impure ix u.

(*
Instance MonadFix_impure `{Provide ix MFIX} : MonadFix (impure ix) :=
  { mfix := @impure_mfix ix _ _ }.
*)

(** And we equip this axiomatized definition with an equation. *)

Axiom mfix_equation
  : forall `{Provide ix MFIX} {t u}
           (rec : (t -> impure ix u) -> t -> impure ix u)
           (x : t),
    mfix rec x = rec (mfix rec) x.

Definition repeat `{Provide ix MFIX} `(h : t -> impure ix (t + u)) (x : t)
  : impure ix u :=
  mfix (fun rec x => let* res := h x in
                     match res with
                     | inl x => rec x
                     | inr x => ret x
                     end) x.

Fixpoint repeat_gas `{Provide ix MFix} `(h : t -> impure ix (t + u)) (x : t) (gas : nat)
  : impure ix (option u) :=
  let* res := h x in
  match gas, res with
  | _, inr x => ret (Some x)
  | S n, inl x => repeat_gas h x n
  | O, _ => ret None
  end.

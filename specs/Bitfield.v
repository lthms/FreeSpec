(* FreeSpec
 * Copyright (C) 2018 ANSSI
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

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Program.Equality.
Require Import Coq.NArith.NArith.

Require Import FreeSpec.Specs.Memory.
Require Import FreeSpec.WEq.

Local Close Scope nat_scope.
Local Open Scope N_scope.

(** * Definitions

    We introduce the [Bitfield] _Indexed_ Monad. A computation of type
    [Bitfield n A] will parse a [mem n] data and returns an [A]. Under
    the hood, a [Bitfield m A] is a function which takes a natural
    number and returns an element of [A].

    ** The Indexed Monad

 *)

Definition Bitfield
           (m: N)
           (A: Type)
  := N -> A.

(** To actually perform the computation, that is parsing some kind of
    memory to read the specified bitfield, the prefered way is to use
    [parse]. It takes a [mem n] of the same size and return the parsed
    bitfield..

 *)

Definition parse
           {A: Type}
           {n:  N}
           (bf: Bitfield n A)
           (x:  mem n)
  : A :=
  bf (unbox x).

(** ** Monadic Oprations

    We define three monadic operations to use with the [Bitfield]
    Indexed Monad:

      - [bf_pure a] to create a [Bitfield 0] computation (parse nothing)
        that always returns [a]
      - [bf_bind p f] to bind two Bitfields together
      - [field n] to parse a field of size [n]
 *)

Definition bf_pure
           {A: Type}
           (a: A)
  : Bitfield 0 A :=
  fun (n:  N)
  => a.

Definition bf_bind
           {m m': N}
           {A B: Type}
           (bf: Bitfield m A)
           (f: A -> Bitfield m' B)
  : Bitfield (m + m') B :=
  fun (n:  N)
  => (f (bf n)) (N.shiftr n m).

Definition field
        (m: N)
  : Bitfield m N :=
  fun (n:  N)
  => n mod 2 ^ m.

(** Indexed Monads are no Monad according to the definition of
    [Monad]. Yet, the [Bitfield] computation has similar
    properties. Therefore, we introduce similar notation.

 *)

Notation "p :>>= f" := (bf_bind p f)
                         (at level 54).
Notation "x :<- p ; q" := (p :>>= fun x => q)
                            (at level 99, right associativity, p at next level).
Notation "p :; q" := (p :>>= fun _ => q)
                            (at level 99, right associativity).

(** ** Additional Computations

    These three oprations can be composed together. For instance, we
    introduce the [skip] operation very easily.

 *)

Definition skip
        (m: N)
  : Bitfield m unit :=
  field m :;
  bf_pure tt.

Definition bit
  : Bitfield 1 bool :=
    x :<- field 1            ;
    if N.eqb x 0
    then bf_pure false
    else bf_pure true.

(** * Control Instances

    Because [Bitfield] is indexed, it cannot be used easily with the
    definition of the [FreeSpec.Control] library. However, the
    [Bitfield] Indexed Monad should have similar properties and we now
    prove these assertion.

    We first define a very strong weak equality, because it is enough
    for now. Maybe we will have to refine this latter.

 *)

(** ** Functor

    For all [n], the [Bitfield n] computation _is_ a [Functor] and it
    is pretty easy to show. Indeed, [Bitfield n] is actually a type
    synonym for a plain function.

 *)

(** ** Applicative

    To be an [Applicative] instance, a computation needs two
    operation: [pure] and [apply]. The [pure] function of [Bitfield]
    has been already defined: it is [bf_pure] (hence the name). As for
    [apply], we define it now using [bf_bind] and our alternative
    do-notation. Fortunately, this makes the implementation pretty
    straightforward.

 *)

Definition bf_apply
           {A B: Type}
           {n m: N}
           (bff: Bitfield n (A -> B))
           (bf: Bitfield m A)
  : Bitfield (n + m) B :=
  f :<- bff            ;
  x :<- bf             ;
  bf_pure (f x).

(** The [Applicative] typeclass comes with several laws we need to
    prove.

 *)

Fact bitfield_applicative_identity
     {A: Type}
     {m: N}
     (x: Bitfield m A)
  : bf_apply (bf_pure id) x = x.
Proof.
  unfold bf_apply, bf_pure, bf_bind, id.
  cbn.
  reflexivity.
Qed.

(** * Examples

 *)

(* Here is an example (yet to be removed latter)
 *)
Definition SMRAMC_bf
  : Bitfield 8 (bool * bool * bool) :=
    skip 4                          :;
    d_lck  :<- bit                   ;
    d_cls  :<- bit                   ;
    d_open :<- bit                   ;
    skip 1                          :;
    bf_pure (d_lck, d_cls, d_open)   .
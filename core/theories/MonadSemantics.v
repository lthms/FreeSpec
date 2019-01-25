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

Require Import FreeSpec.Interface.
Require Import FreeSpec.Semantics.

Require Import Prelude.Control.
Require Import Prelude.Control.Identity.
Require Import Prelude.Control.State.
Require Import Prelude.Equality.

(** * The Semantics Monad

  We define a monadic interface for Semantics. This allows for
  implementing a semantics thanks to the [Control.IO]
  Monad. Unfortunately, the FreeSpec formalism is not quite ready for
  this interface.

 *)

Class MonadSemantics
      (I:  Interface)
      (M:  Type -> Type) :=
  { monadsemantics_is_monad :> Monad M
  ; handle (A: Type):  I A -> M A
  }.

Arguments handle [I M _ A] (_).

(** * Another Stateful Semantics

    Until we find a way to deprecate [Semantics] in favor of
    [MonadSemantics], we can use the State monad to build stateful
    semantics quite easily.

 *)

Definition monad_state_semantics
           {S:     Type} `{Equality S}
           {I:     Interface} `{MonadSemantics I (State S)}
           (init:  S)
  : Semantics I :=
  mkSemantics (fun (A:  Type)
                   (s:  S)
                   (e:  I A)
               => runIdentity (runStateT (m:=Identity) (handle e) s))
              init.

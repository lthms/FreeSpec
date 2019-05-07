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

Require Import Prelude.Control.

Require Import FreeSpec.Component.
Require Import FreeSpec.Compose.
Require Import FreeSpec.Program.

Require Export FreeSpec.Exec.Debug.

Local Open Scope free_scope.
Local Open Scope prelude_scope.

Declare ML Module "freespec_exec".

#[local]
Fixpoint extends
         {Ix J:  Type -> Type}
         {A S:   Type}
         (s:     S)
         (comp:  Component J S Ix)
         (p:     Program (J <+> Ix) A)
: Program Ix (A * S) :=
  match p with
  | Pure x
    => Pure (x, s)
  | Request (InL e) f
    => res <- comp _ e s;
       extends (snd res) comp (f (fst res))
  | Request (InR e) f
    => Request e (fun x => extends s comp (f x))
  end.

(** With FreeSpec.Exec, it becomes possible to interpret a term of type [Program
    Ix A], where [Ix] depends on the plugins loaded by the user.

    In addition, we provide [withComponent], a helper function to extend the set
    of interfaces that can be executed with FreeSpec [Component]s. There are
    several advantages to rely on [withComponent] rather than writing an OCaml
    plugin, the most important being a handler in Coq is not part of the
    TCB. Besides, it can be verified as any FreeSpec [Component]. *)
Definition withComponent
         {Ix J:         Type -> Type}
         {A S:          Type}
         (** A [Component] carries its own state. The [initializer] is a
             computation to construct the initial state of the component *)
         (initializer:  Program Ix S)
         (** The [Component] used to implement a semantics for J *)
         (comp:         Component J S Ix)
         (** The [finalizer] is a clean-up computation to “destruct” the
             [Component] final state *)
         (finalizer:    S -> Program Ix unit)
         (** A computation to interpret, that uses [J] in addition to [Ix]. *)
         (p:            Program (J <+> Ix) A)
  : Program Ix A :=
  s <- initializer;
  res <- extends s comp p;
  finalizer (snd res);;
  pure (fst res).

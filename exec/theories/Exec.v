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

Definition withComponent
         {Ix J:         Type -> Type}
         {A S:          Type}
         (initializer:  Program Ix S)
         (comp:         Component J S Ix)
         (finalizer:    S -> Program Ix unit)
         (p:            Program (J <+> Ix) A)
  : Program Ix A :=
  s <- initializer;
  res <- extends s comp p;
  finalizer (snd res);;
  pure (fst res).

Declare ML Module "exec_plugin".
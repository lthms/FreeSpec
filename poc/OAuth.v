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

Require Import Prelude.Control.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Program.
Require Import FreeSpec.Compose.

Module Type OAuthSpec.
  Parameters (Token:  Type)
             (ID:     Type).
End OAuthSpec.

Module OAuth (Spec:  OAuthSpec).
  Inductive OAuthInterface
  : Interface :=
  | CheckToken (tok:  Spec.Token)
    : OAuthInterface (option Spec.ID).

  Module DSL.
    Definition check_token
               {ix:  Type -> Type} `{Use OAuthInterface ix}
               (tok:  Spec.Token)
    : Program ix (option Spec.ID) :=
      request (CheckToken tok).
  End DSL.
End OAuth.
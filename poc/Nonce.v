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

Require Import Coq.Sets.Ensembles.
Require Import FreeSpec.Specification.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Compose.
Require Import FreeSpec.Program.

Inductive NonceGen
          (A:  Type)
  : Interface :=
| GetNonce
  : NonceGen A A.

Arguments GetNonce [A].

Definition get_nonce
           {a:   Type}
           {ix:  Type -> Type} `{Use (NonceGen a) ix}
  : Program ix a :=
  request GetNonce.

Module NonceSpecification.
  Definition State
             (A:  Type)
  : Type :=
    Ensemble A.

  Definition gen_nonce_postcondition
             {A:      Type}
             (nonce:  A)
             (set:    State A)
    : Prop :=
    ~ In A set nonce.

  Definition gen_nonce_step
             {A:      Type}
             (nonce:  A)
             (set:    State A)
    : State A :=
    Union A (Singleton A nonce) set.

  Definition specification
             (A:  Type)
    : Specification (State A) (NonceGen A) :=
    {| abstract_step := fun (R:      Type)
                            (i:      NonceGen A R)
                            (x:      R)
                            (state:  State A)
                       => match i, x with
                          | GetNonce, x
                            => gen_nonce_step x state
                          end
     ; precondition := no_pre
     ; postcondition := fun (R:      Type)
                            (i:      NonceGen A R)
                            (x:      R)
                            (state:  State A)
                        => match i, x with
                           | GetNonce, x
                             => gen_nonce_postcondition x state
                           end
     |}.
End NonceSpecification.
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

Require Import FreeSpec.Arch.Memory.
Require Import Coq.Init.Nat.
Require Import Coq.NArith.NArith.

(* we only consider 32 bit system *)
Definition address := lword.

Local Close Scope nat_scope.
Local Open Scope N_scope.

Definition is_pow_2
           (n:  N)
  : Prop :=
  2 ^ (N.log2 n) = n.

Program Definition is_aligned
        (x:     address)
        (base:  N | is_pow_2 base)
  : Prop :=
  cast base x = box base 0.

Program Definition aligned_address
        (n:  N | is_pow_2 n)
  : Type :=
  {addr: address | is_aligned addr n}.

Program Definition address_64B_aligned
  : Type :=
  aligned_address 64.
Next Obligation.
  reflexivity.
Defined.
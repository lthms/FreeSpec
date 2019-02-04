(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2018–2019 Thomas Letan <thomas.letan@ssi.gouv.fr>
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
Require Import FreeSpec.Specification.

Require Import Prelude.Equality.

Local Open Scope prelude_scope.

Definition reference_specification
           {I:  Interface}
  : Specification (Sem.t I) I :=
  {| abstract_step := fun (A:  Type)
                          (e:  I A)
                          (_:  A)
                          (s:  Sem.t I)
                      => execEffect s e
  ; precondition := fun (A:  Type)
                         (_:  I A)
                         (_: Sem.t I)
                    => True
  ; postcondition := fun (A:    Type)
                         (e:    I A)
                         (res:  A)
                         (s:    Sem.t I)
                     => evalEffect s e = res
  |}.

Theorem semantics_eq_reference_specification
        {I:    Interface}
        (ref:  Sem.t I)
        (sig:  Sem.t I)
  : sig == ref
    -> sig |= reference_specification [ref].
Proof.
  revert ref sig.
  cofix semantics_eq_reference_specification.
  intros ref sig [Hres Hnext].
  constructor.
  + intros A e Htrue.
    cbn.
    symmetry.
    apply Hres.
  + intros A e Htrue.
    cbn.
    apply semantics_eq_reference_specification.
    apply Hnext.
Qed.

Corollary reference_compliant_reference_specification
          {I:    Interface}
          (ref:  Sem.t I)
  : ref |= reference_specification [ref].
Proof.
  apply semantics_eq_reference_specification.
  reflexivity.
Qed.
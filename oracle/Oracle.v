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

Require Import FreeSpec.Specification.
Require Import FreeSpec.Control.
Require Import FreeSpec.Control.State.
Require Import FreeSpec.Interface.
Require Import FreeSpec.PropBool.
Require Import FreeSpec.MonadSemantics.
Require Import FreeSpec.Control.Classes.

Local Open Scope free_control_scope.
Local Close Scope nat_scope.
Local Open Scope list_scope.

Class SpecificationBool
      {S:  Type}
      {I:  Interface}
      (c:  Specification S I) :=
  { precondition_bool {A:  Type}
    : I A -> S -> bool
  ; postcondition_bool {A:  Type}
    : I A -> A -> S -> bool
  ; req_propbool :> forall (A:  Type),
      PropBool2 (precondition c (A:=A)) (@precondition_bool A)
  ; prom_propbool :> forall (A:  Type),
      PropBool3 (postcondition c (A:=A)) (@postcondition_bool A)
  }.

Arguments precondition_bool [S I] (c) [_ A] (_ _).
Arguments postcondition_bool [S I] (c) [_ A] (_ _ _).

Inductive SemanticsStep
          (I:  Interface)
  : Type :=
| semantics_step {A:    Type}
                 (i:    I A)
                 (res:  A)
  : SemanticsStep I.

Arguments semantics_step [I A] (i res).

Definition step_type
           {I:   Interface}
           (is:  SemanticsStep I)
  : Type :=
  match is with
  | @semantics_step _ A _ _ => A
  end.

Definition step_instr
           {I:   Interface}
           (is:  SemanticsStep I)
  : I (step_type is) :=
  match is with
  | semantics_step i _ => i
  end.

Definition step_ret
           {I:   Interface}
           (is:  SemanticsStep I)
  : step_type is :=
  match is with
  | semantics_step _ x => x
  end.

Definition instruction_picker
           (M:  Type -> Type)
           (I:  Interface) :=
  (forall (A:  Type), I A -> bool) -> M (SemanticsStep I).

Definition test_semantics_once
           {I:     Interface}
           {S:     Type}
           {M:     Type -> Type}
          `{MonadState M S}
           (pick:  instruction_picker M I)
           (c:     Specification S I)
          `{SpecificationBool S I c}
  : M (SemanticsStep I * bool) :=
  s    <- get                                                        ;
  is   <- pick (fun {A:  Type} (i: I A) => precondition_bool c i s)  ;
  modify (abstract_step c (step_instr is) (step_ret is))            ;;
  pure (is, postcondition_bool c (step_instr is) (step_ret is) s).

Fixpoint test_semantics_aux
         {I:     Interface}
         {S:     Type}
         {M:     Type -> Type}
        `{MonadState M S}
         (pick:  instruction_picker M I)
         (c:     Specification S I)
        `{SpecificationBool S I c}
         (n: nat)
         (l: list (SemanticsStep I))
  : M (list (SemanticsStep I) * bool) :=
  match n with
  | O
    => pure (l, true)
  | S m
    => res <- test_semantics_once pick c                           ;
       if (snd res: bool)
       then test_semantics_aux pick c m (fst res :: l)
       else pure (fst res :: l, false)
  end.

Definition test_semantics
           {I:     Interface}
           {S:     Type}
           {M:     Type -> Type}
          `{MonadState M S}
           (pick:  instruction_picker M I)
           (c:     Specification S I)
          `{SpecificationBool S I c}
           (n:     nat)
           (l:     list (SemanticsStep I))
  : M (list (SemanticsStep I) * bool) :=
  test_semantics_aux pick c n nil.
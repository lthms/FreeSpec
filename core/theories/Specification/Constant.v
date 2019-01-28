(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2018 Thomas Letan <thomas.letan@ssi.gouv.fr>
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

Require Import FreeSpec.Semantics.
Require Import FreeSpec.Specification.
Require Import FreeSpec.Program.
Require Import FreeSpec.Abstract.

Definition const_precondition
           {I:             Interface}
           (precondition:  forall (A: Type), I A -> Prop)
  := fun (A:  Type)
         (i:  I A)
         (_:  unit)
     => precondition A i.

Definition const_postcondition
           {I:              Interface}
           (postcondition:  forall (A:  Type)
                                   (e:  I A),
               A -> Prop)
  := fun (A: Type)
         (e: I A)
         (x: A)
         (_: unit)
     => postcondition A e x.

Definition constant_specification
           {I:              Interface}
           (precondition:   forall (A:  Type), I A -> Prop)
           (postcondition:  forall (A:  Type)
                                   (e:  I A),
               A -> Prop)
  : Specification unit I :=
  {| abstract_step  := fun (A: Type) (_: I A) (_: A) (_: unit) => tt
   ; precondition   := @const_precondition I precondition
   ; postcondition  := @const_postcondition I postcondition
   |}.

Definition precondition_preserves_inv
           {I:             Interface}
           {S:             Type}
           (precondition:  forall (A: Type), I A -> Prop)
           (step:          @PS I S)
           (inv:           S -> Prop)
  := forall (A:  Type)
            (e:  I A)
            (s:  S),
    inv s
    -> precondition A e
    -> inv (snd (step A s e)).

Lemma const_specification_preserves_inv
      {I:              Interface}
      {S:              Type}
      (precondition:   forall (A: Type), I A -> Prop)
      (postcondition:  forall (A: Type), I A -> A -> Prop)
      (step:           @PS I S)
      (inv:            S -> Prop)
  : precondition_preserves_inv precondition step inv
    -> specification_preserves_inv (constant_specification precondition postcondition)
                              (fun _ s => inv s)
                              step.
Proof.
  unfold precondition_preserves_inv, specification_preserves_inv.
  intros Hpre.
  intros B e _s s Hinv Hconst.
  apply (Hpre B e s Hinv Hconst).
Qed.

Definition precondition_enforces_postcondition
           {I:              Interface}
           {S:              Type}
           (precondition:   forall (A: Type), I A -> Prop)
           (postcondition:  forall (A: Type), I A -> A -> Prop)
           (step:           @PS I S)
           (inv:            S -> Prop)
  := forall (A:  Type)
            (e:  I A)
            (s:  S),
    inv s
    -> precondition A e
    -> postcondition A e (fst (step A s e)).

Lemma const_specification_enforces_postcondition
      {I:              Interface}
      {S:              Type}
      (precondition:   forall (A: Type), I A -> Prop)
      (postcondition:  forall (A: Type), I A -> A -> Prop)
      (step:           @PS I S)
      (inv:            S -> Prop)
  : precondition_enforces_postcondition precondition postcondition step inv
    -> specification_enforces_postcondition (constant_specification precondition postcondition)
                                            (fun _ s => inv s)
                                            step.
Proof.
  unfold precondition_enforces_postcondition, specification_enforces_postcondition.
  intros Hpre.
  intros B e s _s Hinv Hconst.
  apply (Hpre B e s Hinv Hconst).
Qed.

Lemma const_specification_enforcement
      {I:              Interface}
      {S:              Type}
      (precondition:   forall (A: Type), I A -> Prop)
      (postcondition:  forall (A: Type), I A -> A -> Prop)
      (step:           @PS I S)
      (inv:            S -> Prop)
      (Hpres:          precondition_preserves_inv precondition step inv)
      (Henf:           precondition_enforces_postcondition precondition postcondition step inv)
  : forall (s: S),
    inv s
    -> (mkSemantics step s) |= (constant_specification precondition postcondition)[tt].
Proof.
  intros s Hinv.
  apply (stateful_specification_enforcement (constant_specification precondition postcondition)
                                            tt
                                            (fun _ s => inv s)
                                            step).
  + apply const_specification_preserves_inv.
    exact Hpres.
  + apply const_specification_enforces_postcondition.
    exact Henf.
  + exact Hinv.
Qed.

Fact tt_singleton
     (x y: unit)
  : x = y.
Proof.
  induction x; induction y; reflexivity.
Qed.

Lemma correct_program_compliant_exec
      {I:    Interface}
      {A:    Type}
      (p:    Program I A)
      (c:    Specification unit I)
      (sig:  Semantics I)
  : p =| c[tt]
    -> sig |= c[tt]
    -> (execProgram sig p) |= c[tt].
Proof.
  intros Hc Hcomp.
  apply (compliant_correct_compliant p c tt sig) in Hcomp.
  ++ rewrite abstract_exec_exec_program_same in Hcomp.
     rewrite (tt_singleton (specification_derive p sig c tt) tt) in Hcomp.
     exact Hcomp.
  ++ exact Hc.
Qed.
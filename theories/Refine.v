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
Require Import FreeSpec.Program.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Specification.
Require Import FreeSpec.Abstract.

Require Import Prelude.Control.
Require Import Prelude.Control.State.

(** * Stateful Refinement

    ** Definition
 *)

Definition StatefulRefinement
           (I J:  Interface)
           (S:    Type) :=
  forall (A: Type),
    I A -> StateT S (Program J) A.

Definition StatefulSemantics
           {I J:  Interface}
           {S:    Type}
           (sr:   StatefulRefinement I J S)
           (s:    S)
           (sig:  Semantics J)
  : Semantics I :=
    mkSemantics (fun {A:   Type}
                     (st:  (S * Semantics J))
                     (e:   I A)
                 => ( fst (evalProgram (snd st) (sr A e (fst st)))
                    , ( snd (evalProgram (snd st) (sr A e (fst st)))
                      , (execProgram (snd st) (sr A e (fst st)))
                      )
                    )
                )
                (s, sig).

(** ** Specification Compliance

    We consider so-called “predicates of synchronization” between two
    abstract States [Si] (input) and [So] (output) linked by a
    concrete state [S].
 *)

Definition sync_pred
           (W_I W_J: Type)
           (S: Type)
  := W_I -> S -> W_J -> Prop.

Definition correct_refinement
           {W_I W_J:  Type}
           {I J:      Interface}
           {S:        Type}
           (sr:       StatefulRefinement I J S)
           (master:   Specification W_I I)
           (slave:    Specification W_J J)
           (sync:     sync_pred W_I W_J S) :=
  forall (w_i:  W_I)
         (s:    S)
         (w_j:  W_J)
         {A:    Type}
         (e:    I A),
    sync w_i s w_j
    -> precondition master e w_i
    -> (sr A e s) =| slave[w_j].

Definition sync_preservation
           {W_I W_J:  Type}
           {I J:      Interface}
           {S:        Type}
           (sr:       StatefulRefinement I J S)
           (master:   Specification W_I I)
           (slave:    Specification W_J J)
           (sync:     sync_pred W_I W_J S) :=
  forall (w_i:    W_I)
         (s:      S)
         (w_j:    W_J)
         (sig:    Semantics J)
         (Hcomp:  sig |= slave[w_j])
         {A:      Type}
         (e:      I A),
  sync w_i s w_j
  -> precondition master e w_i
  -> sync (abstract_step master e (fst (evalProgram sig (sr A e s))) w_i)
          (snd (evalProgram sig (sr A e s)))
          (specification_derive (sr A e s) sig slave w_j).

Definition sync_postcondition
           {W_I W_J:  Type}
           {I J:      Interface}
           {S:        Type}
           (sr:       StatefulRefinement I J S)
           (master:   Specification W_I I)
           (slave:    Specification W_J J)
           (sync:     sync_pred W_I W_J S) :=
  forall (w_i:    W_I)
         (s:      S)
         (w_j:    W_J)
         (sig:    Semantics J)
         (Hcomp:  sig |= slave[w_j])
         {A:      Type}
         (e:      I A),
  sync w_i s w_j
  -> precondition master e w_i
  -> postcondition master e (fst (evalProgram sig (sr A e s))) w_i.

Theorem compliant_refinement
        {W_I W_J:    Type}
        {I J:        Interface}
        {S:          Type}
        (sr:         StatefulRefinement I J S)
        (master:     Specification W_I I)
        (slave:      Specification W_J J)
        (sync:       sync_pred W_I W_J S)
        (Hsyncpres:  sync_preservation sr master slave sync)
        (Hsyncp:     sync_postcondition sr master slave sync)
        (Hcorrect:   correct_refinement sr master slave sync)
  : forall (w_i:   W_I)
           (s:    S)
           (w_j:   W_J)
           (sig:  Semantics J)
           (Hcomp: sig |= slave[w_j]),
    sync w_i s w_j
    -> StatefulSemantics sr s sig |= master[w_i].
Proof.
  cofix.
  intros w_i s w_j sig Hcomp Hsync.
  constructor.
  + intros A e Hpre.
    unfold sync_postcondition in Hsyncp.
    assert (evalEffect (StatefulSemantics sr s sig) e
            = fst (evalProgram sig (sr A e s)))
      as Heq by reflexivity.
    rewrite Heq.
    apply (Hsyncp w_i s w_j sig Hcomp A e Hsync Hpre).
  + intros A e Hpre.
    unfold correct_refinement in Hcorrect.
    assert ((sr A e s) =| slave[w_j])
      as Hcp
        by  apply (Hcorrect w_i s w_j A e Hsync Hpre).
    assert (execEffect (StatefulSemantics sr s sig) e
            = StatefulSemantics sr
                                (snd (evalProgram sig (sr A e s)))
                                (execProgram sig (sr A e s)))
      as Hassoc
        by reflexivity.
    rewrite Hassoc.
    apply (compliant_refinement _ _ (specification_derive (sr A e s) sig slave w_j)).
    ++ rewrite <- (abstract_exec_exec_program_same (sr A e s)
                                                   w_j
                                                   (abstract_step slave)
                                                   sig).
       apply (compliant_correct_compliant _ _ _ sig Hcomp Hcp).
    ++ apply Hsyncpres.
       +++ exact Hcomp.
       +++ exact Hsync.
       +++ exact Hpre.
Qed.

(** * Pure Refinement

 *)

Definition PureRefinement
           (I J:  Interface)
  := forall (A:  Type),
    I A -> Program J A.

Fixpoint refine
         {I J:   Interface}
         {A:     Type}
         (p:     Program I A)
         (ref:   PureRefinement I J)
  : Program J A :=
  match p with
  | Pure x
    => Pure x
  | Request e
    => ref _ e
  | Bind q f
    => Bind (refine q ref) (fun x => refine (f x) ref)
  end.

Definition adapt
           {I J K:  Interface}
           {S:      Type}
           (sref:      StatefulRefinement I J S)
           (pref:      PureRefinement J K)
  : StatefulRefinement I K S :=
  fun (A:  Type)
      (e:  I A)
      (s:  S)
  => refine (sref A e s) pref.
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
Require Import FreeSpec.Program.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Specification.

Require Import Prelude.Control.
Require Import Prelude.Control.State.

(** * Modeling Components *)

(** The initial goal of FreeSpec remains to model components (1) which
    exposes and uses interfaces, and (2) which carries their own
    state. To model (1), we rely on the [Program] monad. A Component
    is therefore model as a function that maps operations of the
    [Interface] it exposes to [Program] parameterized with the
    [Interface] it uses. Besides, to model the stateful nature of
    components, we leverage the [StateT] monad. *)
Definition Component
           (I:  Interface)
           (S:  Type)
           (J:  Interface) :=
  forall (A: Type),
    I A -> StateT S (Program J) A.

(** It then becomes possible to turn a component model into a
    semantics for the interface it exposes. *)
Definition ComponentSemantics
           {I J:  Interface}
           {S:    Type}
           (sr:   Component I S J)
           (s:    S)
           (sig:  Sem.t J)
  : Sem.t I :=
    mkSemantics (fun {A:   Type}
                     (st:  (S * Sem.t J))
                     (e:   I A)
                 => ( fst (evalProgram (snd st) (sr A e (fst st)))
                    , ( snd (evalProgram (snd st) (sr A e (fst st)))
                      , (execProgram (snd st) (sr A e (fst st)))
                      )
                    )
                )
                (s, sig).

(** ** Specification Compliance *)

(** This definition of what a [Component] allows for specifying a
    system in terms of inter-connected components. Our motivation to
    use Coq is to leverage its features to _verify_ these components
    and, ultimately, the system as a whole.

    The “local” verification process could be summarized as follows:
    as long as a given component is used in accordance with an
    abstract specification it exposes, it will itself use the
    components it relies on in accordance with their respective
    abstract specifications. Stated this way, we can already see why
    FreeSpec is advertized as a _compositional_ reasoning framework.

    We consider so-called “predicates of synchronization” between two
    witness states [w__i] (input) and [w__j] (output) linked by a concrete
    state [S].*)
Definition sync_pred
           (W_I W_J: Type)
           (S: Type)
  := W_I -> S -> W_J -> Prop.

Definition correct_component
           {W_I W_J:  Type}
           {I J:      Interface}
           {S:        Type}
           (sr:       Component I S J)
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
    -> (sr A e s) |> slave[w_j].

Definition sync_preservation
           {W_I W_J:  Type}
           {I J:      Interface}
           {S:        Type}
           (sr:       Component I S J)
           (master:   Specification W_I I)
           (slave:    Specification W_J J)
           (sync:     sync_pred W_I W_J S) :=
  forall (w_i:    W_I)
         (s:      S)
         (w_j:    W_J)
         (sig:    Sem.t J)
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
           (sr:       Component I S J)
           (master:   Specification W_I I)
           (slave:    Specification W_J J)
           (sync:     sync_pred W_I W_J S) :=
  forall (w_i:    W_I)
         (s:      S)
         (w_j:    W_J)
         (sig:    Sem.t J)
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
        (sr:         Component I S J)
        (master:     Specification W_I I)
        (slave:      Specification W_J J)
        (sync:       sync_pred W_I W_J S)
        (Hsyncpres:  sync_preservation sr master slave sync)
        (Hsyncp:     sync_postcondition sr master slave sync)
        (Hcorrect:   correct_component sr master slave sync)
  : forall (w_i:   W_I)
           (s:    S)
           (w_j:   W_J)
           (sig:  Sem.t J)
           (Hcomp: sig |= slave[w_j]),
    sync w_i s w_j
    -> ComponentSemantics sr s sig |= master[w_i].
Proof.
  cofix compliant_refinement.
  intros w_i s w_j sig Hcomp Hsync.
  constructor.
  + intros A e Hpre.
    unfold sync_postcondition in Hsyncp.
    assert (evalEffect (ComponentSemantics sr s sig) e
            = fst (evalProgram sig (sr A e s)))
      as Heq by reflexivity.
    rewrite Heq.
    apply (Hsyncp w_i s w_j sig Hcomp A e Hsync Hpre).
  + intros A e Hpre.
    unfold correct_component in Hcorrect.
    assert ((sr A e s) |> slave[w_j])
      as Hcp
        by  apply (Hcorrect w_i s w_j A e Hsync Hpre).
    assert (execEffect (ComponentSemantics sr s sig) e
            = ComponentSemantics sr
                                (snd (evalProgram sig (sr A e s)))
                                (execProgram sig (sr A e s)))
      as Hassoc
        by reflexivity.
    rewrite Hassoc.
    apply (compliant_refinement _ _ (specification_derive (sr A e s) sig slave w_j)).
    ++ now apply correct_program_compliant_semantics_compliant_semantics.
    ++ apply Hsyncpres.
       +++ exact Hcomp.
       +++ exact Hsync.
       +++ exact Hpre.
Qed.
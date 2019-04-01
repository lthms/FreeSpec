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

Require Import Coq.Setoids.Setoid.

Require Import FreeSpec.Interface.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Program.
Require Import FreeSpec.Specification.

Require Import Prelude.Equality.
Require Import Prelude.Control.

Local Open Scope prelude_scope.

(** * [Interface] Composition

 *)
Inductive IntCompose
          (I J:  Interface)
          (A:    Type)
  : Type :=
| InL (e: I A)
  : IntCompose I J A
| InR (e: J A)
  : IntCompose I J A.

Arguments InL [I J A] (e).
Arguments InR [I J A] (e).

(** Let [I] and [J] be two Interfaces. [I <+> J] denotes the
    [Interface] which unifies [I] and [J].

 *)

Infix "<+>" :=
  (IntCompose)
    (at level 50, left associativity)
  : free_scope.

Local Open Scope free_scope.

Instance IntCompose_Use_L
         (ix i j:  Interface)
        `{Use i ix}
  : Use i (ix <+> j) :=
  { lift_eff := fun (a:  Type)
                    (e:  i a)
                => InL (lift_eff e)
  }.

Instance IntCompose_Use_R
         (j i jx:  Interface)
        `{Use j jx}
  : Use j (i <+> jx) :=
  { lift_eff := fun (a:  Type)
                    (e:  j a)
                => InR (lift_eff e)
  }.

(** * Operational Semantics

    It is easy to derive an operational [Semantics] for [I <+> J] with
    one semantics for [I] and one for [J].

    ** Proof-friendly Semantics

 *)

CoFixpoint mkCompSemantics
           {I J:    Interface}
           (sig_i:  Sem.t I)
           (sig_j:  Sem.t J)
  : Sem.t (I <+> J) :=
  Sem.handler
    (fun {A: Type} (e: I <+> J $ A)
     => match e with
        | InL e_i
          => let res := handle sig_i e_i in
             Sem.mkRes (Sem.res res)
                       (mkCompSemantics (Sem.next res) sig_j)
        | InR e_j
          =>  let res := handle sig_j e_j in
              Sem.mkRes (Sem.res res)
                        (mkCompSemantics sig_i (Sem.next res))
        end).

(** We define three morphisms. Just in case. By doing so, we will be
    able to use the [rewrite] tactic to replace one operational
    semantics with an equivalent one.

 *)

Add Parametric Morphism
    (I J:  Interface)
  : (@mkCompSemantics I J)
    with signature (@equal (Sem.t I) _) ==> (@equal (Sem.t J) _) ==> (@equal (Sem.t $ I <+> J) _)
      as mk_comp_semantics_complete_morphism.
Proof.
  cofix mk_comp_semantics_complete_morphism.
  intros sig_1 sig_2 Heq sig_1' sig_2' Heq'.
  constructor.
  + intros A e.
    unfold mkCompSemantics.
    induction e;
      cbn; [ rewrite Heq | rewrite Heq' ];
      reflexivity.
  + intros A e.
    induction e;
      cbn.
    ++ assert (execEffect sig_1 e == execEffect sig_2 e). {
         rewrite Heq.
         reflexivity.
       }
       apply (mk_comp_semantics_complete_morphism (execEffect sig_1 e)
                                                  (execEffect sig_2 e)
                                                  H
                                                  sig_1'
                                                  sig_2'
                                                  Heq').
    ++ assert (execEffect sig_1' e == execEffect sig_2' e). {
         rewrite Heq'.
         reflexivity.
       }
       apply (mk_comp_semantics_complete_morphism sig_1
                                                  sig_2
                                                  Heq
                                                  (execEffect sig_1' e)
                                                  (execEffect sig_2' e)
                                                  H).
Qed.

Infix "<x>" :=
  (mkCompSemantics)
    (at level 50, left associativity)
  : free_scope.

(** * Abstract Specification Composition

    Because Interfaces can be composed together, abstract
    Specifications need their composition operator too.

 *)

Definition compose_step
           {W_I W_J:  Type}
           {I J:      Interface}
           (step_i:   forall {A: Type}, I A -> A -> W_I -> W_I)
           (step_j:   forall {A: Type}, J A -> A -> W_J -> W_J)
           (A:        Type)
           (e:        (I <+> J) A)
           (x:        A)
           (w:        W_I * W_J)
  : W_I * W_J :=
  match w, e with
  | (w_i, w_j), InL e_i =>
    (step_i e_i x w_i, w_j)
  | (w_i, w_j), InR e_j =>
    (w_i, step_j e_j x w_j)
  end.

Definition compose_precondition
           {W_I W_J:  Type}
           {I J:      Interface}
           (pre_i:    forall {A: Type}, I A -> W_I -> Prop)
           (pre_j:    forall {A: Type}, J A -> W_J -> Prop)
           (A:        Type)
           (e:        (I <+> J) A)
           (w:        W_I * W_J)
  : Prop :=
  match w, e with
  | (w_i, _), InL e_i =>
    pre_i e_i w_i
  | (_, w_j), InR e_j =>
    pre_j e_j w_j
  end.

Definition compose_postcondition
           {W_I W_J:  Type}
           {I J:      Interface}
           (post_i:   forall {A: Type} (i: I A), A -> W_I -> Prop)
           (post_j:   forall {A: Type} (i: J A), A -> W_J -> Prop)
           (A:        Type)
           (e:        (I <+> J) A)
           (x:        A)
           (w:        W_I * W_J)
  : Prop :=
  match w, e with
  | (w_i, _), InL e_i
    => post_i e_i x w_i
  | (_, w_j), InR e_j
    => post_j e_j x w_j
  end.

Definition composeSpecification
           {W_I W_J:  Type}
           {I J:      Interface}
           (c_i:      Specification W_I I)
           (c_j:      Specification W_J J)
  : Specification (W_I * W_J) (I <+> J) :=
  {| abstract_step  := compose_step (abstract_step c_i) (abstract_step c_j)
   ; precondition   := compose_precondition (precondition c_i) (precondition c_j)
   ; postcondition  := compose_postcondition (postcondition c_i) (postcondition c_j)
   |}.

Infix "<·>" :=
  (composeSpecification)
    (at level 50, left associativity)
  : free_scope.

Lemma compliant_semantics_compose_compliant_semantics
      {W_I W_J:  Type}
      {I J:      Interface}
  : forall (sig_i:  Sem.t I)
           (sig_j:  Sem.t J)
           (c_i:    Specification W_I I)
           (c_j:    Specification W_J J)
           (w_i:    W_I)
           (w_j:    W_J),
    sig_i |= c_i[w_i]
    -> sig_j |= c_j[w_j]
    -> sig_i <x> sig_j |= (c_i <·> c_j)[(w_i, w_j)].
Proof.
  cofix compliant_semantics_compose_compliant_semantics.
  intros sig_i sig_j c_i c_j w_i w_j Hsig_i Hsig_j.
  constructor.
  + intros A e Hpre.
    induction e; cbn; cbn in Hpre.
    ++ apply compliant_enforces_postcondition; [ exact Hsig_i
                                               | exact Hpre
                                               ].
    ++ apply compliant_enforces_postcondition; [ exact Hsig_j
                                               | exact Hpre
                                               ].
  + intros A e Hpre.
    induction e; cbn; cbn in *.
    ++ apply compliant_semantics_compose_compliant_semantics; [| apply Hsig_j].
       inversion Hsig_i.
       apply (Henf A e Hpre).
    ++ apply compliant_semantics_compose_compliant_semantics; [apply Hsig_i |].
       inversion Hsig_j.
       apply (Henf A e Hpre).
Qed.

(** ** Left

 *)

Definition expand_step_left
           {W:     Type}
           {I:     Interface}
           (step:  forall {A: Type} (i: I A), A -> W -> W)
           (J:     Interface)
           (A:     Type)
           (e:     (I <+> J) A)
           (x:     A)
           (w:     W)
  : W :=
  match e with
  | InL e_i
    => step e_i x w
  | _
    => w
  end.

Definition expand_pre_left
           {W:    Type}
           {I:    Interface}
           (pre:  forall {A: Type}, I A -> W -> Prop)
           (J:    Interface)
           (A:    Type)
           (e:    (I <+> J) A)
           (w:    W)
  : Prop :=
  match e with
  | InL e_i
    => pre e_i w
  | _
    => True
  end.

Definition expand_post_left
           {W:     Type}
           {I:     Interface}
           (post:  forall {A: Type} (i: I A), A -> W -> Prop)
           (J:     Interface)
           (A:     Type)
           (e:     (I <+> J) A)
           (x:     A)
           (w:     W)
  : Prop :=
  match e with
  | InL e_i
    => post e_i x w
  | _
    => True
  end.

Definition expand_specification_left
           {W:  Type}
           {I:  Interface}
           (c:  Specification W I)
           (J:  Interface)
  : Specification W (I <+> J) :=
  {| abstract_step  := expand_step_left (abstract_step c) J
   ; precondition   := expand_pre_left (precondition c) J
   ; postcondition  := expand_post_left (postcondition c) J
   |}.

Lemma expand_compliant_left
  : forall {W:      Type}
           {I J:    Interface}
           {c:      Specification W I}
           {w:      W}
           {sig_i:  Sem.t I}
           (Hcomp:  sig_i |= c[w])
           (sig_j:  Sem.t J),
    sig_i <x> sig_j |= (expand_specification_left c J)[w].
Proof.
  cofix expand_compliant_left.
  intros S I J c w sig_i Hcomp sig_j.
  assert (Hcomp': sig_i |= c[w]) by apply Hcomp.
  destruct Hcomp.
  constructor.
  + intros A e; induction e; cbn; [| trivial].
    apply Hprom.
  + intros A e Hpre.
    induction e; cbn.
    ++ apply expand_compliant_left.
       apply Henf.
       exact Hpre.
    ++ apply expand_compliant_left.
       exact Hcomp'.
Qed.

(** ** Right

 *)

Definition expand_step_right
           {W:     Type}
           {I:     Interface}
           (step:  forall {A: Type} (i: I A), A -> W -> W)
           (J:     Interface)
           (A:     Type)
           (e:     (J <+> I) A)
           (x:     A)
           (w:     W)
  : W :=
  match e with
  | InR e_i
    => step e_i x w
  | _
    => w
  end.

Definition expand_pre_right
           {W:    Type}
           {I:    Interface}
           (pre:  forall {A: Type}, I A -> W -> Prop)
           (J:    Interface)
           (A:    Type)
           (e:    (J <+> I) A)
           (w:    W)
  : Prop :=
  match e with
  | InR e_i
    => pre e_i w
  | _
    => True
  end.

Definition expand_post_right
           {W:     Type}
           {I:     Interface}
           (post:  forall {A: Type} (i: I A), A -> W -> Prop)
           (J:     Interface)
           (A:     Type)
           (e:     (J <+> I) A)
           (x:     A)
           (w:     W)
  : Prop :=
  match e with
  | InR e_i
    => post e_i x w
  | _
    => True
  end.

Definition expand_specification_right
           {W:  Type}
           {I:  Interface}
           (c:  Specification W I)
           (J:  Interface)
  : Specification W (J <+> I) :=
  {| abstract_step  := expand_step_right (abstract_step c) J
   ; precondition   := expand_pre_right (precondition c) J
   ; postcondition  := expand_post_right (postcondition c) J
   |}.

Lemma expand_compliant_right
  : forall {W:      Type}
           {I J:    Interface}
           {c:      Specification W I}
           {w:      W}
           {sig_i:  Sem.t I}
           (Hcomp:  sig_i |= c[w])
           (sig_j:  Sem.t J),
    sig_j <x> sig_i |= (expand_specification_right c J)[w].
Proof.
  cofix expand_compliant_right.
  intros S I J c w sig_i Hcomp sig_j.
  assert (Hcomp': sig_i |= c[w]) by apply Hcomp.
  destruct Hcomp.
  constructor.
  + intros A e; induction e; cbn; [trivial |].
    apply Hprom.
  + intros A e Hpre.
    induction e; cbn.
    ++ apply expand_compliant_right.
       exact Hcomp'.
    ++ apply expand_compliant_right.
       apply Henf.
       exact Hpre.
Qed.

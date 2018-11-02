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

Require Import Coq.Program.Equality.

Require Import FreeSpec.Abstract.
Require Import FreeSpec.Specification.
Require Import FreeSpec.Specification.Constant.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Program.
Require Import FreeSpec.Refine.

Require Import Prelude.Control.
Require Import Prelude.Equality.

Local Open Scope prelude_scope.

Inductive sequence
          (I:  Interface)
  : Type :=
| sequence_nil
  : sequence I
| sequence_cons {A:     Type}
                (e:     I A)
                (rest:  sequence I)
  : sequence I.

Arguments sequence_nil [I].
Arguments sequence_cons [I A] (e rest).

Inductive correct_sequence
          {I:    Interface}
          (req:  forall (A:  Type),
              I A -> Prop)
  : sequence I -> Prop :=
| correct_sequence_cons {A:      Type}
                        (e:      I A)
                        (Hreq:   req A e)
                        (rest:   sequence I)
                        (H:      correct_sequence req rest)
  : correct_sequence req (sequence_cons e rest)
| correct_sequence_nil
  : correct_sequence req sequence_nil.

Notation "l '=¦' req" :=
  (correct_sequence req l)
    (at level 50, no associativity).

Fixpoint sequence_to_prog
         {I:   Interface}
         (st:  sequence I)
  : Program I unit :=
  match st with
  | sequence_nil
    => pure tt
  | sequence_cons i rest
    => Request i >>= fun _ => sequence_to_prog rest
  end.

CoInductive stream
            (I:  Interface)
  : Type :=
| stream_cons (seq:       sequence I)
              (infinite:  stream I)
  : stream I.

Arguments stream_cons [I] (seq infinite).

CoInductive correct_stream
            {I:    Interface}
            (req:  forall (A:  Type),
                I A -> Prop)
  : stream I -> Prop :=
| restricted_stream_cons (seq:   sequence I)
                         (Hseq:  correct_sequence req seq)
                         (next:  stream I)
                         (Hnext:  correct_stream req next)
  : correct_stream req (stream_cons seq next).

Notation "st '*=¦' req" :=
  (correct_stream req st)
    (at level 50, no associativity).

Definition pick
           {I:   Interface}
           (st:  stream I)
  : sequence I :=
  match st with
  | stream_cons seq _
    => seq
  end.

Definition consume
           {I:   Interface}
           (st:  stream I)
  : stream I :=
  match st with
  | stream_cons _ infinite
    => infinite
  end.

Fact correct_stream_pick_correct_sequence
     {I:    Interface}
     (req:  forall (A:  Type), I A -> Prop)
     (st:   stream I)
     (H:    st *=¦ req)
  : pick st =¦ req.
Proof.
  inversion H; subst.
  exact Hseq.
Qed.

Fact correct_stream_consume_correct_stream
     {I:    Interface}
     (req:  forall (A:  Type), I A -> Prop)
     (st:   stream I)
     (H:    st *=¦ req)
  : consume st *=¦ req.
Proof.
  inversion H; subst.
  exact Hnext.
Qed.

CoFixpoint concurrent_semantics
         {I:    Interface}
         (sig:  Semantics I)
         (st:   stream I)
  : Semantics I :=
  handler (fun {A:  Type}
               (e:  I A)
           => (evalEffect (execProgram sig (sequence_to_prog (pick st))) e,
               concurrent_semantics (execEffect (execProgram sig
                                                             (sequence_to_prog (pick st))
                                                ) e)
                                    (consume st))).

Inductive non_interference_requirement
          {W:    Type}
          {I:    Interface}
          (c:    Specification W I)
          (req:  forall (A:  Type), I A -> Prop)
  : Prop :=
| concurrent_semanticss_req (Hreq: forall {A:  Type}
                                          (i:  I A)
                                          (w:  W),
                                req A i -> precondition c i w)
                            (Hni: forall {A:  Type}
                                         (i:  I A)
                                         (x:  A)
                                         (w:  W),
                                req A i -> abstract_step c i x w = w)
  : non_interference_requirement c req.

Notation "c \\ req" :=
  (non_interference_requirement c req)
    (at level 50, no associativity, req at next level).

Lemma correct_sequence_rewrite_abstract_state
      {I:     Interface}
      {W:     Type}
      (w:     W)
      (c:     Specification W I)
      (req:   forall (A:  Type),
          I A -> Prop)
      (seq:   sequence I)
      (Hseq:  seq =¦ req)
      (sig:   Semantics I)
      (Hsig:  sig |= c[w])
      (Hni:   c \\ req)
  : specification_derive (sequence_to_prog seq) sig c w = w.
Proof.
  revert Hsig; revert sig w.
  induction seq; intros sig w Hsig.
  + reflexivity.
  + cbn.
    unfold program_bind.
    rewrite <- specification_derive_bind.
    inversion Hseq; simplify_eqs; simpl_existTs; subst.
    rewrite IHseq.
    ++ apply Hni.
       apply Hreq.
    ++ apply H0.
    ++ apply compliant_correct_compliant; [ exact Hsig |].
       constructor.
       destruct Hni.
       apply Hreq0.
       exact Hreq.
Qed.

Lemma correct_sequence_correct_program
      {I:     Interface}
      {W:     Type}
      (w:     W)
      (c:     Specification W I)
      (req:   forall (A:  Type),
          I A -> Prop)
      (seq:   sequence I)
      (Hseq:  seq =¦ req)
      (Hni:   c \\ req)
  : sequence_to_prog seq =| c[w].
Proof.
  revert w.
  induction seq; intros w.
  + constructor.
  + cbn.
    unfold program_bind.
    constructor.
    ++ inversion Hseq; simplify_eqs; simpl_existTs; subst.
       constructor.
       destruct Hni.
       apply Hreq0.
       exact Hreq.
    ++ intros int Hint.
       inversion Hseq; simplify_eqs; simpl_existTs; subst.
       assert (Heq:  specification_derive (Request e) int c w = w). {
         cbn.
         destruct Hni.
         apply Hni.
         apply Hreq.
       }
       rewrite Heq.
       apply IHseq.
       exact H0.
Qed.

Theorem concurrence_is_possible
        {I:     Interface}
        {W:     Type}
        (w:     W)
        (c:     Specification W I)
        (req:   forall (A:  Type),
            I A -> Prop)
        (st:    stream I)
        (Hst:   st *=¦ req)
        (sig:   Semantics I)
        (Hsig:  sig |= c[w])
        (Hni:   c \\ req)
  : concurrent_semantics sig st |= c[w].
Proof.
  revert Hsig.
  revert Hst.
  revert sig st w.
  cofix concurrence_is_possible; intros sig st w Hst Hsig.
  constructor.
  + cbn.
    assert (pick st =¦ req)
      by (apply correct_stream_pick_correct_sequence; assumption).
    assert (consume st *=¦ req)
      by (apply correct_stream_consume_correct_stream; assumption).
    inversion Hst; subst.
    cbn.
    intros A e Hpre.
    erewrite <- correct_sequence_rewrite_abstract_state; [ idtac
                                                         | exact Hseq
                                                         | exact Hsig
                                                         | exact Hni
                                                         ].
    erewrite <- correct_sequence_rewrite_abstract_state in Hpre; [ idtac
                                                         | exact Hseq
                                                         | exact Hsig
                                                         | exact Hni
                                                         ].
    assert (Hsig': execProgram sig (sequence_to_prog seq) |= c[specification_derive (sequence_to_prog seq) sig c w]). {
      erewrite <- abstract_exec_exec_program_same.
      apply compliant_correct_compliant.
      exact Hsig.
      apply correct_sequence_correct_program with (req0 :=  req).
      + exact Hseq.
      + exact Hni.
    }
    apply Hsig'.
    apply Hpre.
  + cbn.
    assert (pick st =¦ req)
      by (apply correct_stream_pick_correct_sequence; assumption).
    assert (consume st *=¦ req)
      by (apply correct_stream_consume_correct_stream; assumption).
    inversion Hst; subst.
    cbn.
    intros A e Hpre.
    remember (execProgram sig (sequence_to_prog seq)) as sig'.
    remember (evalEffect sig' e) as x.
    assert (Hp:  sequence_to_prog seq =| c[w]). {
      apply correct_sequence_correct_program with (req0 :=  req).
      exact Hseq.
      exact Hni.
    }
    assert (Hsig':  sig' |= c[w]). {
      rewrite <- (correct_sequence_rewrite_abstract_state w c req seq Hseq sig Hsig Hni).
      rewrite Heqsig'.
      erewrite <- abstract_exec_exec_program_same.
      apply compliant_correct_compliant.
      + exact Hsig.
      + exact Hp.
    }
    apply concurrence_is_possible.
    apply Hnext.
    rewrite Heqx.
    apply Hsig'.
    apply Hpre.
Qed.
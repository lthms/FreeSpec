Require Import Coq.Program.Equality.

Require Import FreeSpec.Abstract.
Require Import FreeSpec.Contract.
Require Import FreeSpec.Contract.Constant.
Require Import FreeSpec.Control.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Program.
Require Import FreeSpec.Refine.
Require Import FreeSpec.WEq.

Local Open Scope free_weq_scope.

Inductive sequence
          (I:  Interface)
  : Type :=
| sequence_nil
  : sequence I
| sequence_cons {A:     Type}
                (i:     I A)
                (rest:  sequence I)
  : sequence I.

Arguments sequence_nil [I].
Arguments sequence_cons [I A] (i rest).

Inductive correct_sequence
          {I:    Interface}
          (req:  forall (A:  Type),
              I A -> Prop)
  : sequence I -> Prop :=
| correct_sequence_cons {A:      Type}
                        (i:      I A)
                        (Hreq:   req A i)
                        (rest:   sequence I)
                        (H:      correct_sequence req rest)
  : correct_sequence req (sequence_cons i rest)
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
    => instr i >>= fun _ => sequence_to_prog rest
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

CoFixpoint concurrent_interp
         {I:    Interface}
         (int:  Interp I)
         (st:   stream I)
  : Interp I :=
  interp (fun {A:  Type}
              (i:  I A)
          => (evalInstruction (execProgram int (sequence_to_prog (pick st))) i,
              concurrent_interp (execInstruction (execProgram int
                                                              (sequence_to_prog (pick st))
                                                 ) i)
                                (consume st))).

Inductive non_interference_requirement
          {W:    Type}
          {I:    Interface}
          (c:    Contract W I)
          (req:  forall (A:  Type), I A -> Prop)
  : Prop :=
| concurrent_contracts_req (Hreq: forall {A:  Type}
                                         (i:  I A)
                                         (w:  W),
                               req A i -> requirements c i w)
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
      (c:     Contract W I)
      (req:   forall (A:  Type),
          I A -> Prop)
      (seq:   sequence I)
      (Hseq:  seq =¦ req)
      (int:   Interp I)
      (Hint:  int |= c[w])
      (Hni:   c \\ req)
  : contract_derive (sequence_to_prog seq) int c w = w.
Proof.
  revert Hint; revert int w.
  induction seq; intros int w Hint.
  + reflexivity.
  + cbn.
    unfold program_bind.
    rewrite <- contract_derive_pbind.
    inversion Hseq; simplify_eqs; simpl_existTs; subst.
    rewrite IHseq.
    ++ apply Hni.
       apply Hreq.
    ++ apply H0.
    ++ apply enforcer_compliant_enforcer; [ exact Hint |].
       constructor.
       destruct Hni.
       apply Hreq0.
       exact Hreq.
Qed.

Lemma correct_sequence_correct_program
      {I:     Interface}
      {W:     Type}
      (w:     W)
      (c:     Contract W I)
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
       assert (Heq:  contract_derive (instr i) int c w = w). {
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
        (c:     Contract W I)
        (req:   forall (A:  Type),
            I A -> Prop)
        (st:    stream I)
        (Hst:   st *=¦ req)
        (int:   Interp I)
        (Hint:  int |= c[w])
        (Hni:   c \\ req)
  : concurrent_interp int st |= c[w].
Proof.
  revert Hint.
  revert Hst.
  revert int st w.
  cofix; intros int st w Hst Hint.
  constructor.
  + cbn.
    assert (pick st =¦ req)
      by (apply correct_stream_pick_correct_sequence; assumption).
    assert (consume st *=¦ req)
      by (apply correct_stream_consume_correct_stream; assumption).
    inversion Hst; subst.
    cbn.
    intros A i Hreq.
    erewrite <- correct_sequence_rewrite_abstract_state; [ idtac
                                                         | exact Hseq
                                                         | exact Hint
                                                         | exact Hni
                                                         ].
    erewrite <- correct_sequence_rewrite_abstract_state in Hreq; [ idtac
                                                         | exact Hseq
                                                         | exact Hint
                                                         | exact Hni
                                                         ].
    assert (Hint': execProgram int (sequence_to_prog seq) |= c[contract_derive (sequence_to_prog seq) int c w]). {
      erewrite <- abstract_exec_exec_program_same.
      apply enforcer_compliant_enforcer.
      exact Hint.
      apply correct_sequence_correct_program with (req0 :=  req).
      + exact Hseq.
      + exact Hni.
    }
    apply Hint'.
    apply Hreq.
  + cbn.
    assert (pick st =¦ req)
      by (apply correct_stream_pick_correct_sequence; assumption).
    assert (consume st *=¦ req)
      by (apply correct_stream_consume_correct_stream; assumption).
    inversion Hst; subst.
    cbn.
    intros A i Hreq.
    remember (execProgram int (sequence_to_prog seq)) as int'.
    remember (evalInstruction int' i) as x.
    assert (Hp:  sequence_to_prog seq =| c[w]). {
      apply correct_sequence_correct_program with (req0 :=  req).
      exact Hseq.
      exact Hni.
    }
    assert (Hint':  int' |= c[w]). {
      rewrite <- (correct_sequence_rewrite_abstract_state w c req seq Hseq int Hint Hni).
      rewrite Heqint'.
      erewrite <- abstract_exec_exec_program_same.
      apply enforcer_compliant_enforcer.
      + exact Hint.
      + exact Hp.
    }
    apply concurrence_is_possible.
    apply Hnext.
    rewrite Heqx.
    apply Hint'.
    apply Hreq.
Qed.
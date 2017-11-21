Require Import Coq.Program.Equality.

Require Import FreeSpec.Abstract.
Require Import FreeSpec.Contract.
Require Import FreeSpec.Control.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Program.

(** * Regular Execution

 *)

Inductive Execution
          {I:    Interface}
          {A:    Type}
          (int:  Interp I)
  : Program I A -> A -> Interp I -> Prop :=
| exec_ret (x:  A)
  : Execution int (ret x) x int
| exec_instr (i:  I A)
  : Execution int (instr i) (evalInstruction int i) (execInstruction int i)
| exec_bind {B:           Type}
            (p:           Program I B)
            (f:           B -> Program I A)
            (x:           B)
            (y:           A)
            (int' int'':  Interp I)
            (Hleft:       @Execution I B int p x int')
            (Hright:      Execution int' (f x) y int'')
  : Execution int (pbind p f) y int''.

Theorem exec_prop_exec_comp
        {I:    Interface}
        {A:    Type}
        (int:  Interp I)
        (p:    Program I A)
  : Execution int p (evalProgram int p) (execProgram int p).
Proof.
  revert int;
    induction p;
    intros int.
  + constructor.
  + constructor.
  + rewrite eval_program_bind_assoc.
    rewrite exec_program_bind_assoc.
    apply exec_bind with (x:=evalProgram int p)
                         (int':=execProgram int p).
    ++ apply IHp.
    ++ apply H.
Qed.

Theorem exec_prop_unique_res
        {I:           Interface}
        {A:           Type}
        (int:         Interp I)
        (p:           Program I A)
        (x y:         A)
        (int' int'':  Interp I)
  : Execution int p x int'
    -> Execution int p y int''
    -> x = y /\ int' = int''.
Proof.
  revert int int' int''.
  induction p; intros int int' int''.
  + intros H1 H2.
    inversion H1; subst.
    inversion H2; subst.
    split; reflexivity.
  + intros H1 H2.
    inversion H1; subst.
    inversion H2; subst.
    split; reflexivity.
  + intros H1 H2.
    inversion H1; simplify_eqs; simpl_existTs.
    inversion H2; simplify_eqs; simpl_existTs.
    subst.
    assert (Hx:  x0 = x1 /\ int'0 = int'1). {
      apply IHp with (int:=int); [ apply Hleft
                                 | apply Hleft0
                                 ].
    }
    destruct Hx as [Hx Hint].
    subst.
    apply H with (b:=x1)
                 (int:=int'1); [ apply Hright
                               | apply Hright0
                               ].
Qed.

Inductive stream
          {I:  Interface}
          (P:  forall (A:  Type), I A -> Prop)
  : Type :=
| stop
  : stream P
| pick {A:     Type}
       (i:     I A)
       (H:     P A i)
       (rest:  stream P)
  : stream P.

Arguments stop [I P].
Arguments pick [I P A] (i H rest).

Fixpoint stream_to_prog
         {I:   Interface}
         {P:   forall (A:  Type), I A -> Prop}
         (st:  stream P)
  : Program I unit :=
  match st with
  | stop
    => pure tt
  | pick i _ rest
    => instr i >>= fun _ => stream_to_prog rest
  end.

Inductive ConcurrentExecution
          {I:    Interface}
          {A:    Type}
          (int:  Interp I)
          (P:    forall (A:  Type),
              I A -> Prop)
  : Program I A -> A -> Interp I -> Prop :=
| conc_exec_ret (x:  A)
  : ConcurrentExecution int P (ret x) x int
| conc_exec_instr (st:    stream P)
                  (int':  Interp I)
                  (Hst:   Execution int (stream_to_prog st) tt int')
                  (i:     I A)
  : ConcurrentExecution int P (instr i) (evalInstruction int' i) (execInstruction int' i)
| conc_exec_bind {B:           Type}
                 (p:           Program I B)
                 (f:           B -> Program I A)
                 (x:           B)
                 (y:           A)
                 (int' int'':  Interp I)
                 (Hleft:       @ConcurrentExecution I B int P p x int')
                 (Hright:      ConcurrentExecution int' P (f x) y int'')
  : ConcurrentExecution int P (pbind p f) y int''.

Theorem execution_is_concurrent_execution
        {I:         Interface}
        {A:         Type}
        (int int':  Interp I)
        (p:         Program I A)
        (x:         A)
  : forall (P:  forall (A:  Type),
               I A -> Prop),
    Execution int p x int'
    -> ConcurrentExecution int P p x int'.
Proof.
  intros P.
  revert int int' x; induction p; intros int int' x.
  + intros H.
    inversion H; subst.
    constructor.
  + intros H.
    inversion H; subst.
    apply conc_exec_instr with (st:=stop).
    constructor.
  + intros Hbind.
    inversion Hbind; simplify_eqs; simpl_existTs.
    subst.
    apply IHp in Hleft.
    apply H in Hright.
    apply conc_exec_bind with (x1:=x0)
                              (int'1:=int'0); [ apply Hleft
                                              | apply Hright
                                              ].
Qed.

Notation "int '-[' p ']->' int'" :=
  (Execution int (p >>= fun _ => pure tt) tt int')
    (at level 50, no associativity).

Notation "int '=[' p '||' P ']=>' int'" :=
  (ConcurrentExecution int P (p >>= fun _ => pure tt) tt int')
    (at level 50, no associativity).

(** * Abstract Execution

 *)

Inductive AbstractExecution
          {I:    Interface}
          {A W:  Type}
          (c:    Contract W I)
  : W -> Program I A -> A -> W -> Prop :=
| abstract_exec_ret (w:  W)
                    (x:  A)
  : AbstractExecution c w (ret x) x w
| abstract_exec_instr (w:      W)
                      (i:      I A)
                      (Hreq:   requirements c i w)
                      (x:      A)
                      (Hprom:  promises c i x w)
  : AbstractExecution c w (instr i) x (abstract_step c i x w)
| abstract_exec_bind {B:         Type}
                     (w w' w'':  W)
                     (p:         Program I B)
                     (x:         B)
                     (f:         B -> Program I A)
                     (y:         A)
                     (Hright:    AbstractExecution (A:=B) c w p x w')
                     (Hleft:     AbstractExecution c w' (f x) y w'')
  : AbstractExecution c w (pbind p f) y w''.

Lemma compliant_interpreter_correct_program_abstract_execution
      {I:     Interface}
      {A W:   Type}
      (c:     Contract W I)
      (w:     W)
      (int:   Interp I)
      (p:     Program I A)
      (Hint:  int |= c[w])
      (Hp:    p =| c[w])
  : AbstractExecution c w p (evalProgram int p) (contract_derive p int c w).
Proof.
  revert Hp Hint.
  revert w int.
  induction p; intros w int Hp Hint.
  + constructor.
  + constructor; [| apply Hint ];
      inversion Hp;
      simplify_eqs;
      simpl_existTs;
      subst;
      exact Hreq.
  + rewrite <- contract_derive_pbind.
    rewrite eval_program_bind_assoc.
    apply abstract_exec_bind with (w' :=  contract_derive p int c w)
                                  (x  :=  evalProgram int p).
    ++ apply IHp; [| apply Hint ].
       apply correct_pbind_correct_left_operand with (f0:=f).
       apply Hp.
    ++ rewrite abstract_exec_exec_program_same.
       apply H.
       apply correct_pbind_correct_right_operand; [ exact Hint
                                                  | exact Hp
                                                  ].
       erewrite <- abstract_exec_exec_program_same.
       apply enforcer_compliant_enforcer.
       exact Hint.
       apply correct_pbind_correct_left_operand with (f0 :=  f).
       exact Hp.
Qed.

Inductive ConcurrentAbstractExecution
          {I:    Interface}
          {A W:  Type}
          (c:    Contract W I)
          (P:    forall (A:  Type),
              I A -> Prop)
  : W -> Program I A -> A -> W -> Prop :=
| concur_abstract_exec_ret (w:  W)
                           (x:  A)
  : ConcurrentAbstractExecution c P w (ret x) x w
| concur_abstract_exec_instr (w w':     W)
                             (st:       stream P)
                             (Hbefore:  AbstractExecution c w (stream_to_prog st) tt w')
                             (i:        I A)
                             (Hreq:     requirements c i w')
                             (x:        A)
                             (Hprom:    promises c i x w')
  : ConcurrentAbstractExecution c P w' (instr i) x (abstract_step c i x w')
| concur_abstract_exec_bind {B:         Type}
                            (w w' w'':  W)
                            (p:         Program I B)
                            (x:         B)
                            (f:         B -> Program I A)
                            (y:         A)
                            (Hright:    ConcurrentAbstractExecution (A:=B) c P w p x w')
                            (Hleft:     ConcurrentAbstractExecution c P w' (f x) y w'')
  : ConcurrentAbstractExecution c P w (pbind p f) y w''.

Theorem abstract_execution_is_concurrent_abstract_execution
        {I:    Interface}
        {A W:  Type}
        (c:    Contract W I)
        (w:    W)
        (P:    forall (A:  Type), I A -> Prop)
        (p:    Program I A)
        (x:    A)
        (w':   W)
  : AbstractExecution c w p x w'
    -> ConcurrentAbstractExecution c P w p x w'.
Proof.
  revert w w'.
  induction p; intros w w'.
  + intros H; inversion H; subst.
    constructor.
  + intros H; inversion H; subst.
    eapply concur_abstract_exec_instr with (w0 :=  w)
                                           (st :=  stop).
    ++ constructor.
    ++ exact Hreq.
    ++ exact Hprom.
  + intros Hbind.
    inversion Hbind;
      simplify_eqs;
      simpl_existTs;
      subst.
    apply concur_abstract_exec_bind with (w'1 :=  w'0)
                                         (x1  :=  x0).
    ++ apply IHp.
       exact Hright.
    ++ apply H.
       apply Hleft.
Qed.
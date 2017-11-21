Require Import Coq.Program.Equality.

Require Import FreeSpec.Control.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Program.

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
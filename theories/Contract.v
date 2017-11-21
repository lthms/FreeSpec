(* begin hide *)
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Logic.Classical.
(* end hide *)

Require Import FreeSpec.Program.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Abstract.

(** * Contract Definition

    A Contract permits to define an expected behaviour for an
    [Interface] [Interp]reter. This behaviour is expressed with two
    complementary predicates:

    - The [requirements] an [Interface] user has to enforce
    - The [promises] an [Interp]reter has to hold in case the
      [requirements] are effectively met

    These predicates are tied to an abstract state. This abstract
    state is modified by the [abstract_step] function through the
    execution (see [abstractRun] for more information about that).

 *)

Record Contract
       (S: Type)
       (I: Interface)
  :=
    { abstract_step (A: Type)
                    (i: I A)
                    (a: A)
      : S -> S
    ; requirements (A: Type)
      : I A -> S -> Prop
    ; promises (A: Type)
      : I A -> A -> S -> Prop
    }.

Arguments abstract_step [_ _] (_) [_] (_ _ _).
Arguments requirements [_ _] (_) [_] (_ _).
Arguments promises [_ _] (_) [_] (_ _).

Definition contract_derive
           {S:   Type}
           {I:   Interface}
           {A:   Type}
           (p:   Program I A)
           (int: Interp I)
           (c:   Contract S I)
           (s:   S)
  : S :=
  deriveAbstraction s (abstract_step c) int p.

Fact contract_derives_ret_eq
     {S:   Type}
     {I:   Interface}
     {A:   Type}
     (a:   A)
     (int: Interp I)
     (c:   Contract S I)
     (s:   S)
  : contract_derive (ret a) int c s = s.
Proof.
  reflexivity.
Qed.

Fact contract_derives_contract_step
     {S:   Type}
     {I:   Interface}
     {A:   Type}
     (i:   I A)
     (int: Interp I)
     (c:   Contract S I)
     (s:   S)
  : contract_derive (instr i) int c s = abstract_step c i (evalInstruction int i) s.
Proof.
  reflexivity.
Qed.

(** ** Contract Compliance

    An Interpreter is a [compliant_interpreter] of a given [Contract]
    [c] if it enforces the contract [promises] as long as its
    [requirements] are met by the caller. The Contract Enforcement is
    parameterized by an abstract state and, by definition, if an
    Interpreter enforces a [Contract] [c] and executes a primitive
    which meets the [requirements] of [c], then the resulting
    Interpreter will enforces [c] for the new abstract state returned
    by the [abstract_step] function.

 *)

CoInductive compliant_interpreter
            {S:   Type}
            {I:   Interface}
            (c:   Contract S I)
            (s:   S)
            (int: Interp I)
  : Prop :=
| enforced (Hprom: forall {A: Type}
                          (i: I A),
               requirements c i s
               -> (promises c i) (evalInstruction int i) s)
           (Henf:  forall {A: Type}
                          (i: I A),
               requirements c i s
               -> compliant_interpreter c
                           (abstract_step c i (evalInstruction int i) s)
                           (execInstruction int i))
  : compliant_interpreter c s int.

Notation "int '|=' c '[' s ']'" :=
  (compliant_interpreter c s int)
    (at level 60, no associativity).

Corollary enforcer_enforces_promises
      {S:    Type}
      {I:    Interface}
      {A:    Type}
      (i:    I A)
      (int:  Interp I)
      (c:    Contract S I)
      (s:    S)
      (Henf: int |= c[s])
      (Hreq: requirements c i s)
  : promises c i (evalInstruction int i) s.
Proof.
  destruct Henf.
  apply Hprom.
  exact Hreq.
Qed.

(** ** Compliant Stateful Interpreter

 *)

Definition contract_preserves_inv
           {S:     Type}
           {I:     Interface}
           {State: Type}
           (c:     Contract S I)
           (inv:   S -> State -> Prop)
           (step:  @PS I State)
  := forall (A:   Type)
            (i:   I A)
            (abs: S)
            (s:   State),
    inv abs s
    -> requirements c i abs
    -> inv (abstract_step c i (fst (step A s i)) abs) (snd (step A s i)).

Definition contract_enforces_promises
           {S:     Type}
           {I:     Interface}
           {State: Type}
           (c:     Contract S I)
           (inv:   S -> State -> Prop)
           (step:  @PS I State)
  := forall (A:   Type)
            (i:   I A)
            (s:   State)
            (abs: S),
    inv abs s
    -> requirements c i abs
    -> promises c i (fst (step A s i)) abs.

Fact _stateful_contract_enforcement
     {S:     Type}
     {I:     Interface}
     {State: Type}
     (c:     Contract S I)
     (inv:   S -> State -> Prop)
     (step:  @PS I State)
  : forall (abs:   S)
           (Hpres: contract_preserves_inv c inv step)
           (Henf:  contract_enforces_promises c inv step)
           (s:     State),
    inv abs s
    -> (mkInterp step s) |= c[abs].
Proof.
  cofix.
  intros abs Hpres Henf s Hinv .
  constructor.
  + intros A i Hreq.
    unfold contract_enforces_promises in Henf.
    cbn in *.
    apply (Henf A i s abs Hinv Hreq).
  + intros A i Hreq.
    apply _stateful_contract_enforcement.
    ++ apply  Hpres.
    ++ apply  Henf.
    ++ cbn in *.
       apply (Hpres _ _ _ _ Hinv Hreq).
Qed.

Lemma stateful_contract_enforcement
      {I:     Interface}
      {S:     Type}
      {State: Type}
      (c:     Contract S I)
      (abs:   S)
      (inv:   S -> State -> Prop)
      (step:  @PS I State)
      (Hpres: contract_preserves_inv c inv step)
      (Henf:  contract_enforces_promises c inv step)
  : forall (s: State),
    inv abs s
    -> (mkInterp step s) |= c[abs].
Proof.
  intros s Hinv.
  apply (_stateful_contract_enforcement c inv step abs Hpres Henf s Hinv).
Qed.


(** * Correct Program

    In a nutshell, a given [Program] is said correct against a given
    [Contract] [c] if, for any compliant interpreter of [c], the
    called primitive always meet the [requirements] of [c].

    ** Definition

 *)

Inductive correct_program
          {S: Type}
          {I: Interface}
          (c: Contract S I)
          (s: S)
  : forall {A: Type}, Program I A -> Prop :=
| compliant_instr {A:    Type}
                  (i:    I A)
                  (Hreq: requirements c i s)
  : correct_program c s (instr i)
| tl_compliant_ret {A: Type}
                   (a: A)
  : correct_program c s (ret a)
| tl_compliant_inv {A B: Type}
                   (p:     Program I A)
                   (f:     A -> Program I B)
                   (Hcp:   correct_program c s p)
                   (Hnext: forall (int: Interp I)
                                  (Henf: int |= c[s]),
                       correct_program c
                                         (contract_derive p int c s)
                                         (f (evalProgram int p)))
  : correct_program c s (pbind p f).

Notation "p '=|' c '[' s ']'" :=
  (correct_program c s p)
    (at level 59, no associativity).

(** ** Enforcement Preservation

    In order to prove the [enforcer_compliant_enforcer] lemmas, we
    first highlight several convenient properties of compliant_interpreter
    interpreters and compliant programs.

 *)

Fact compliant_program_pbind_ret
     {S:   Type}
     {I:   Interface}
     {A B: Type}
     (a:   A)
     (f:   A -> Program I B)
     (c:   Contract S I)
     (s:   S)
  : f a =| c[s]
    -> pbind (ret a) f =| c[s].
Proof.
  intros Hp.
  constructor.
  + constructor.
  + intros int Henf.
    cbn.
    exact Hp.
Qed.

Fact enforcer_instruction_compliant_enforcer
     {S:   Type}
     {I:   Interface}
     {A:   Type}
     (i:   I A)
     (int: Interp I)
     (c:   Contract S I)
     (s:   S)
     (H:   int |= c[s])
     (Hp:  instr i =| c[s])
  : (abstractExec s (abstract_step c) int (instr i))
      |= c[contract_derive (instr i) int c s].
Proof.
  cbn.
  constructor.
  + intros B i' Hinst.
    destruct H as [Hprom Henf].
    inversion Hp.
    apply Henf in Hreq.
    apply inj_pair2 in H1.
    subst.
    inversion Hreq.
    apply Hprom0.
    exact Hinst.
  + intros B i' Hinst.
    destruct H as [Hprom Henf].
    inversion Hp.
    apply Henf in Hreq.
    apply inj_pair2 in H1.
    subst.
    inversion Hreq.
    apply Henf0.
    exact Hinst.
Qed.

Fact enforcer_ret_compliant_enforcer
     {S:   Type}
     {I:   Interface}
     {A:   Type}
     (a:   A)
     (int: Interp I)
     (c:   Contract S I)
     (s:   S)
     (H:   int |= c[s])
  : abstractExec s (abstract_step c) int (ret a)
      |= c[contract_derive (ret a) int c s].
Proof.
  rewrite (contract_derives_ret_eq a int c).
  exact H.
Qed.

Fact contract_derive_assoc
     {S:     Type}
     {I:     Interface}
     {A B C: Type}
     (p:     Program I A)
     (f:     A -> Program I B)
     (f':    B -> Program I C)
     (int:   Interp I)
     (c:     Contract S I)
     (s:     S)
  : contract_derive (pbind (pbind p f) f') int c s
    = contract_derive (pbind p (fun x => pbind (f x) f')) int c s.
Proof.
  reflexivity.
Qed.

Fact exec_abs_assoc
     {S: Type}
     {I: Interface}
     {A: Type}
     (p: Program I A)
  : forall {B:   Type}
           (f:   A -> Program I B)
           (int: Interp I)
           (c:   Contract S I)
           (s:   S),
    abstractExec s (abstract_step c) int (pbind p f)
    = abstractExec (contract_derive p int c s)
                   (abstract_step c)
                   (abstractExec s (abstract_step c) int p)
                   (f (evalProgram int p)).
Proof.
  intros B f int c s.
  repeat rewrite abstract_exec_exec_program_same.
  reflexivity.
Qed.

Fact eval_program_assoc
     {S: Type}
     {I: Interface}
     {A: Type}
     (p: Program I A)
  : forall {B:   Type}
           (f:   A -> Program I B)
           (int: Interp I)
           (c:   Contract S I)
           (s:   S),
    evalProgram int (pbind p f)
    = evalProgram (abstractExec s (abstract_step c) int p)
                  (f (evalProgram int p)).
Proof.
  intros B f int c s.
  rewrite abstract_exec_exec_program_same.
  reflexivity.
Qed.

Fact contract_derive_pbind
     {S: Type}
     {I: Interface}
     {A: Type}
     (p: Program I A)
  : forall {B:   Type}
           (f:   A -> Program I B)
           (int: Interp I)
           (c:   Contract S I)
           (s:   S),
    contract_derive (f (evalProgram int p))
                    (abstractExec s (abstract_step c) int p)
                    c
                    (contract_derive p int c s)
    = contract_derive (pbind p f) int c s.
Proof.
  induction p.
  + reflexivity.
  + reflexivity.
  + intros C f' int' c' s'.
    rewrite contract_derive_assoc.
    rewrite <- (IHp C) .
    rewrite <- H.
    rewrite <- eval_program_assoc.
    rewrite <- exec_abs_assoc.
    rewrite <- (IHp A) .
    reflexivity.
Qed.

Fact abstractExec_pbind
     {S:   Type}
     {I:   Interface}
     {A B: Type}
     (p:   Program I A)
  : forall (f:   A -> Program I B)
           (int: Interp I)
           (c:   Contract S I)
           (s:   S),
    abstractExec (contract_derive p int c s)
                 (abstract_step c)
                 (abstractExec s
                               (abstract_step c)
                               int
                               p)
                 (f (evalProgram int p))
    = abstractExec s (abstract_step c) int (pbind p f).
Proof.
  intros f int c s.
  repeat rewrite abstract_exec_exec_program_same.
  reflexivity.
Qed.

Lemma enforcer_compliant_enforcer
      {S: Type}
      {I: Interface}
      {A: Type}
      (p: Program I A)
  : forall (c:   Contract S I)
           (s:   S)
           (int: Interp I)
           (H:   int |= c[s])
           (Hp:  p =| c[s]),
    (abstractExec s (abstract_step c) int p) |= c[contract_derive p int c s].
Proof.
  induction p.
  + intros c s int He Hp;
      apply (enforcer_ret_compliant_enforcer a int c s He).
  + intros c s int He Hp;
      apply (enforcer_instruction_compliant_enforcer i int c s He Hp).
  + intros c s int He Hp.
    inversion Hp;
      apply inj_pair2 in H3;
      repeat apply inj_pair2 in H4;
      subst.
    apply (IHp c s int He) in Hcp.
    rewrite <- abstractExec_pbind.
    rewrite <- contract_derive_pbind.
    apply H.
    ++ exact Hcp.
    ++ apply Hnext.
       exact He.
Qed.

Lemma correct_pbind_correct_left_operand
      {W:    Type}
      {I:    Interface}
      {A B:  Type}
      (w:    W)
      (c:    Contract W I)
      (p:    Program I A)
      (f:    A -> Program I B)
  : pbind p f =| c[w]
    -> p =| c[w].
Proof.
  intros H.
  inversion H; simplify_eqs; simpl_existTs; subst.
  exact Hcp.
Qed.

Lemma correct_pbind_correct_right_operand
      {W:    Type}
      {I:    Interface}
      {A B:  Type}
      (w:    W)
      (c:    Contract W I)
      (p:    Program I A)
      (f:    A -> Program I B)
      (int:  Interp I)
      (Hint:  int |= c [w])
  : pbind p f =| c [w]
    -> f (evalProgram int p) =| c [contract_derive p int c w].
Proof.
  intros H.
  inversion H; simplify_eqs; simpl_existTs; subst.
  apply Hnext.
  exact Hint.
Qed.

Definition no_req
           {I:  Interface}
           {W:  Type}
           (A:  Type)
           (i:  I A)
           (w:  W)
  : Prop :=
  True.

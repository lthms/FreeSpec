Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Logic.Classical.

Require Import FreeSpec.Program.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Abstract.

Record Contract
       (S: Type)
       (I: Type -> Type)
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
           {S: Type}
           {I: Type -> Type}
           {A: Type}
           (p: Program I A)
           (int: Interp I)
           (c: Contract S I)
           (s: S)
  : S :=
  deriveAbstraction s (abstract_step c) int p.

Lemma contract_derives_ret_eq
      {S: Type}
      {I: Type -> Type}
      {A: Type}
      (a: A)
      (int: Interp I)
      (c: Contract S I)
      (s: S)
  : contract_derive (ret a) int c s = s.
Proof.
  reflexivity.
Qed.

Lemma contract_derives_contract_step
      {S: Type}
      {I: Type -> Type}
      {A: Type}
      (i: I A)
      (int: Interp I)
      (c: Contract S I)
      (s: S)
  : contract_derive (instr i) int c s = abstract_step c i (evalInstruction int i) s.
Proof.
  reflexivity.
Qed.

CoInductive Enforcer
            {S: Type}
            {I: Type -> Type}
            (int: Interp I)
            (c: Contract S I)
            (s: S)
  : Prop :=
| enforced (Hprom: forall {A: Type}
                          (i: I A),
               requirements c i s
               -> (promises c i) (evalInstruction int i) s)
           (Henf:  forall {A: Type}
                          (i: I A),
               requirements c i s
               -> Enforcer (execInstruction int i) c (abstract_step c i (evalInstruction int i) s))
  : Enforcer int c s.

Lemma enforcer_enforces_promises
      {S: Type}
      {I: Type -> Type}
      {A: Type}
      (i: I A)
      (int: Interp I)
      (c: Contract S I)
      (s: S)
      (Henf: Enforcer int c s)
      (Hreq: requirements c i s)
  : promises c i (evalInstruction int i) s.
Proof.
  destruct Henf.
  apply Hprom.
  exact Hreq.
Qed.

Inductive contractfull_program
          {S: Type}
          {I: Type -> Type}
          (c: Contract S I)
          (s: S)
  : forall {A: Type}, Program I A -> Prop :=
| contractfull_instr {A: Type}
                        (i: I A)
                        (Hreq: requirements c i s)
  : contractfull_program c s (instr i)
| tl_contractfull_ret {A: Type}
                      (a: A)
  : contractfull_program c s (ret a)
| tl_contractfull_inv {A B: Type}
                      (p: Program I A)
                      (f: A -> Program I B)
                      (Hcp: contractfull_program c s p)
                      (Hnext: forall (int: Interp I)
                                     (Henf: Enforcer int c s),
                          contractfull_program c
                                               (contract_derive p int c s)
                                               (f (evalProgram int p)))
  : contractfull_program c s (bind p f).

Lemma contractfull_program_bind_ret
      {S: Type}
      {I: Type -> Type}
      {A B: Type}
      (a: A)
      (f: A -> Program I B)
      (c: Contract S I)
      (s: S)
  : contractfull_program c s (f a) -> contractfull_program c s (bind (ret a) f).
Proof.
  intros Hp.
  constructor.
  + constructor.
  + intros int Henf.
    cbn.
    exact Hp.
Qed.

Lemma enforcer_instruction_contractfull_enforcer
      {S: Type}
      {I: Type -> Type}
      {A: Type}
      (i: I A)
      (int: Interp I)
      (c: Contract S I)
      (s: S)
      (H: Enforcer int c s)
      (Hp: contractfull_program c s (instr i))
  : Enforcer (abstractExec s (abstract_step c) int (instr i)) c (contract_derive (instr i) int c s).
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

Lemma enforcer_ret_contractfull_enforcer
      {S: Type}
      {I: Type -> Type}
      {A: Type}
      (a: A)
      (int: Interp I)
      (c: Contract S I)
      (s: S)
      (H: Enforcer int c s)
  : Enforcer (abstractExec s (abstract_step c) int (ret a)) c (contract_derive (ret a) int c s).
Proof.
  rewrite (contract_derives_ret_eq a int c).
  exact H.
Qed.

Lemma contract_derive_assoc
      {S: Type}
      {I: Type -> Type}
      {A B C: Type}
      (p: Program I A)
      (f: A -> Program I B)
      (f': B -> Program I C)
      (int: Interp I)
      (c: Contract S I)
      (s: S)
  : contract_derive (bind (bind p f) f') int c s
    = contract_derive (bind p (fun x => bind (f x) f')) int c s.
Proof.
  reflexivity.
Qed.

Lemma exec_program_assoc'
      {S: Type}
      {I: Type -> Type}
      {A: Type}
      (p: Program I A)
  : forall {B C: Type}
           (f: A -> Program I B)
           (f': B -> Program I C)
           (int: Interp I),
    execProgram int (bind (bind p f) f')
    = execProgram int (bind p (fun x => (bind (f x) f'))).
Proof.
  intros B C f f' int.
  reflexivity.
Qed.

Lemma exec_abs_assoc
      {S: Type}
      {I: Type -> Type}
      {A: Type}
      (p: Program I A)
  : forall {B: Type}
           (f: A -> Program I B)
           (int: Interp I)
           (c: Contract S I)
           (s: S),
    abstractExec s (abstract_step c) int (bind p f)
    = abstractExec (contract_derive p int c s)
                   (abstract_step c)
                   (abstractExec s (abstract_step c) int p)
                   (f (evalProgram int p)).
Proof.
  intros B f int c s.
  repeat rewrite abstract_exec_exec_program_same.
  reflexivity.
Qed.

Lemma eval_program_assoc
      {S: Type}
      {I: Type -> Type}
      {A: Type}
      (p: Program I A)
  : forall {B: Type}
           (f: A -> Program I B)
           (int: Interp I)
           (c: Contract S I)
           (s: S),
    evalProgram int (bind p f)
    = evalProgram (abstractExec s (abstract_step c) int p)
                  (f (evalProgram int p)).
Proof.
  intros B f int c s.
  rewrite abstract_exec_exec_program_same.
  reflexivity.
Qed.

Lemma contract_derive_bind
      {S: Type}
      {I: Type -> Type}
      {A: Type}
      (p: Program I A)
  : forall {B: Type}
           (f: A -> Program I B)
           (int: Interp I)
           (c: Contract S I)
           (s: S),
    contract_derive (f (evalProgram int p))
                    (abstractExec s (abstract_step c) int p)
                    c
                    (contract_derive p int c s)
    = contract_derive (bind p f) int c s.
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

Lemma abstractExec_bind
      {S: Type}
      {I: Type -> Type}
      {A B: Type}
      (p: Program I A)
  : forall (f: A -> Program I B)
           (int: Interp I)
           (c: Contract S I)
           (s: S),
    abstractExec (contract_derive p int c s)
                 (abstract_step c)
                 (abstractExec s
                               (abstract_step c)
                               int
                               p)
                 (f (evalProgram int p))
    = abstractExec s (abstract_step c) int (bind p f).
Proof.
  intros f int c s.
  repeat rewrite abstract_exec_exec_program_same.
  reflexivity.
Qed.

Lemma enforcer_contractfull_enforcer
      {S: Type}
      {I: Type -> Type}
      {A: Type}
      (p: Program I A)
  : forall (c: Contract S I)
           (s: S)
           (int: Interp I)
           (H: Enforcer int c s)
           (Hp: contractfull_program c s p),
    Enforcer (abstractExec s (abstract_step c) int p) c (contract_derive p int c s).
Proof.
  induction p.
  + intros c s int He Hp;
      apply (enforcer_ret_contractfull_enforcer a int c s He).
  + intros c s int He Hp;
      apply (enforcer_instruction_contractfull_enforcer i int c s He Hp).
  + intros c s int He Hp.
    inversion Hp;
      apply inj_pair2 in H3;
      repeat apply inj_pair2 in H4;
      subst.
    apply (IHp c s int He) in Hcp.
    rewrite <- abstractExec_bind.
    rewrite <- contract_derive_bind.
    apply H.
    ++ exact Hcp.
    ++ apply Hnext.
       exact He.
Qed.

Definition contract_preserves_inv
           {S: Type}
           {I: Type -> Type}
           {State: Type}
           (c: Contract S I)
           (inv: S -> State -> Prop)
           (step: @PS I State)
  := forall (A: Type)
            (i: I A)
            (abs: S)
            (s: State),
    inv abs s
    -> requirements c i abs
    -> inv (abstract_step c i (fst (step A s i)) abs) (snd (step A s i)).

Definition contract_enforces_promises
           {S: Type}
           {I: Type -> Type}
           {State: Type}
           (c: Contract S I)
           (inv: S -> State -> Prop)
           (step: @PS I State)
  := forall (A: Type)
            (i: I A)
            (s: State)
            (abs: S),
    inv abs s
    -> requirements c i abs
    -> promises c i (fst (step A s i)) abs.

Fact _stateful_contract_enforcement
     {S: Type}
     {I: Type -> Type}
     {State: Type}
     (c: Contract S I)
     (inv: S -> State -> Prop)
     (step: @PS I State)
  : forall (abs: S)
           (Hpres: contract_preserves_inv c inv step)
           (Henf: contract_enforces_promises c inv step)
           (s: State),
    inv abs s
    -> Enforcer (mkInterp step s) c abs.
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
      {I: Interface}
      {S: Type}
      {State: Type}
      (c: Contract S I)
      (abs: S)
      (inv: S -> State -> Prop)
      (step: @PS I State)
      (Hpres: contract_preserves_inv c inv step)
      (Henf: contract_enforces_promises c inv step)
  : forall (s: State),
    inv abs s
    -> Enforcer (mkInterp step s) c abs.
Proof.
  intros s Hinv.
  apply (_stateful_contract_enforcement c inv step abs Hpres Henf s Hinv).
Qed.

Definition strongly_compliant_program
           {I: Interface}
           {A: Type}
           {Sa: Type}
           (c: Contract Sa I)
           (s: Sa)
           (p: Program I A)
  := contractfull_program c s p
     /\ (forall (int: Interp I),
            Enforcer int c s
            -> Enforcer (execProgram int p) c s).

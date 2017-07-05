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
    { abstract
      : S
    ; abstract_step (A: Type)
                    (i: I A)
      : S -> S
    ; requirements (A: Type)
      : I A -> S -> Prop
    ; promises (A: Type)
      : I A -> A -> S -> Prop
    }.

Arguments abstract [_ _] (_).
Arguments abstract_step [_ _] (_) [_].
Arguments requirements [_ _] (_) [_] (_ _).
Arguments promises [_ _] (_) [_] (_ _).

Definition set_abstract
           {S: Type}
           {I: Type -> Type}
           (c: Contract S I)
           (abs: S)
  : Contract S I :=
  {| abstract := abs
   ; abstract_step := abstract_step c
   ; requirements := requirements c
   ; promises := promises c
  |}.

Definition contract_step
           {S: Type}
           {I: Type -> Type}
           {A: Type}
           (c: Contract S I)
           (i: I A)
  : Contract S I :=
  {| abstract := abstract_step c i (abstract c)
   ; abstract_step := abstract_step c
   ; requirements := requirements c
   ; promises := promises c
  |}.

Definition contract_derive
           {S: Type}
           {I: Type -> Type}
           {A: Type}
           (p: Program I A)
           (int: Interp I)
           (c: Contract S I)
  : Contract S I :=
  {| abstract := deriveAbstraction (abstract c) (abstract_step c) int p
   ; abstract_step := abstract_step c
   ; requirements := requirements c
   ; promises := promises c
  |}.

Lemma contract_derives_ret_eq
      {S: Type}
      {I: Type -> Type}
      {A: Type}
      (a: A)
      (int: Interp I)
      (c: Contract S I)
  : contract_derive (ret a) int c = c.
Proof.
  induction c.
  split.
Qed.

Lemma contract_derives_contract_step
      {S: Type}
      {I: Type -> Type}
      {A: Type}
      (i: I A)
      (int: Interp I)
      (c: Contract S I)
  : contract_derive (instr i) int c = contract_step c i.
Proof.
  unfold contract_derive, contract_step.
  reflexivity.
Qed.

CoInductive Enforcer
            {S: Type}
            {I: Type -> Type}
            (int: Interp I)
  : Contract S I -> Prop :=
| enforced (c: Contract S I)
           (Hprom: forall {A: Type}
                          (i: I A),
               requirements c i (abstract c)
               -> (promises c i) (evalInstruction int i) (abstract c))
           (Henf:  forall {A: Type}
                          (i: I A),
               requirements c i (abstract c)
               -> Enforcer (execInstruction int i) (contract_step c i))
  : Enforcer int c.

Lemma enforcer_enforces_promises
      {S: Type}
      {I: Type -> Type}
      {A: Type}
      (i: I A)
      (int: Interp I)
      (c: Contract S I)
      (Henf: Enforcer int c)
      (Hreq: requirements c i (abstract c))
  : promises c i (evalInstruction int i) (abstract c).
Proof.
  destruct Henf.
  apply Hprom.
  exact Hreq.
Qed.

Inductive contractfull_program
          {S: Type}
          {I: Type -> Type}
          (c: Contract S I)
  : forall {A: Type}, Program I A -> Prop :=
| contractfull_instr {A: Type}
                        (i: I A)
                        (Hreq: requirements c i (abstract c))
  : contractfull_program c (instr i)
| tl_contractfull_ret {A: Type}
                      (a: A)
  : contractfull_program c (ret a)
| tl_contractfull_inv {A B: Type}
                      (p: Program I A)
                      (f: A -> Program I B)
                      (Hcp: contractfull_program c p)
                      (Hnext: forall (int: Interp I)
                                     (Henf: Enforcer int c),
                          contractfull_program (contract_derive p int c) (f (evalProgram int p)))
  : contractfull_program c (bind p f).

Lemma contractfull_program_bind_ret
      {S: Type}
      {I: Type -> Type}
      {A B: Type}
      (a: A)
      (f: A -> Program I B)
      (c: Contract S I)
  : contractfull_program c (f a) -> contractfull_program c (bind (ret a) f).
Proof.
  intros Hp.
  constructor.
  + constructor.
  + intros int Henf.
    cbn.
    rewrite contract_derives_ret_eq.
    exact Hp.
Qed.

Lemma enforcer_instruction_contractfull_enforcer
      {S: Type}
      {I: Type -> Type}
      {A: Type}
      (i: I A)
      (int: Interp I)
      (c: Contract S I)
      (H: Enforcer int c)
      (Hp: contractfull_program c (instr i))
  : Enforcer (abstractExec (abstract c) (abstract_step c) int (instr i)) (contract_derive (instr i) int c).
Proof.
  cbn.
  constructor.
  + intros B i' Hinst.
    destruct H as [c Hprom Henf].
    inversion Hp.
    apply Henf in Hreq.
    apply inj_pair2 in H1.
    subst.
    inversion Hreq.
    rewrite contract_derives_contract_step.
    apply Hprom0.
    exact Hinst.
  + intros B i' Hinst.
    destruct H as [c Hprom Henf].
    inversion Hp.
    apply Henf in Hreq.
    apply inj_pair2 in H1.
    subst.
    inversion Hreq.
    rewrite contract_derives_contract_step.
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
      (H: Enforcer int c)
  : Enforcer (abstractExec (abstract c) (abstract_step c) int (ret a)) (contract_derive (ret a) int c).
Proof.
  rewrite (contract_derives_ret_eq a int c).
  unfold abstractExec.
  cbn.
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
  : contract_derive (bind (bind p f) f') int c
    = contract_derive (bind p (fun x => bind (f x) f')) int c.
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
           (c: Contract S I),
    abstractExec (abstract c) (abstract_step c) int (bind p f)
    = abstractExec (abstract (contract_derive p int c))
                   (abstract_step (contract_derive p int c))
                   (abstractExec (abstract c) (abstract_step c) int p)
                   (f (evalProgram int p)).
Proof.
  intros B f int c.
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
           (c: Contract S I),
    evalProgram int (bind p f)
    = evalProgram (abstractExec (abstract c) (abstract_step c) int p)
                  (f (evalProgram int p)).
Proof.
  intros B f int c.
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
           (c: Contract S I),
    contract_derive (f (evalProgram int p))
                    (abstractExec (abstract c) (abstract_step c) int p) (contract_derive p int c)
    = contract_derive (bind p f) int c.
Proof.
  induction p.
  + reflexivity.
  + reflexivity.
  + intros C f' int' c'.
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
           (c: Contract S I),
    abstractExec (abstract (contract_derive p int c))
                 (abstract_step (contract_derive p int c))
                 (abstractExec (abstract c)
                               (abstract_step c)
                               int
                               p)
                 (f (evalProgram int p))
    = abstractExec (abstract c) (abstract_step c) int (bind p f).
Proof.
  intros f int c.
  repeat rewrite abstract_exec_exec_program_same.
  reflexivity.
Qed.

Lemma enforcer_contractfull_enforcer
      {S: Type}
      {I: Type -> Type}
      {A: Type}
      (p: Program I A)
  : forall (c: Contract S I)
           (int: Interp I)
           (H: Enforcer int c)
           (Hp: contractfull_program c p),
    Enforcer (abstractExec (abstract c) (abstract_step c) int p) (contract_derive p int c).
Proof.
  induction p.
  + intros c int He Hp;
      apply (enforcer_ret_contractfull_enforcer a int c He).
  + intros c int He Hp;
      apply (enforcer_instruction_contractfull_enforcer i int c He Hp).
  + intros c int He Hp.
    inversion Hp;
      apply inj_pair2 in H3;
      repeat apply inj_pair2 in H4;
      subst.
    apply (IHp c int He) in Hcp.
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
           (requirements: forall (R: Type), I R -> S -> Prop)
           (abs_step: forall (R: Type), I R -> S -> S)
           (inv: S -> State -> Prop)
           (step: @PS I State)
  := forall (A: Type)
            (i: I A)
            (abs: S)
            (s: State),
    inv abs s
    -> requirements A i abs
    -> inv (abs_step A i abs) (snd (step A s i)).

Lemma contract_preserves_inv_propagates
      {S: Type}
      {I: Type -> Type}
      {State: Type}
      (inv: S -> State -> Prop)
      (step: @PS I State)
  : forall {A: Type}
           (c: Contract S I)
           (i: I A),
    contract_preserves_inv (requirements c) (abstract_step c) inv step
    -> requirements c i (abstract c)
    -> contract_preserves_inv (requirements (contract_step c i)) (abstract_step (contract_step c i)) inv step.
Proof.
  intros A c i Hpres Hreq.
  unfold contract_preserves_inv in *.
  intros B i' s Hinv Hreq'.
  apply Hpres.
  exact Hreq'.
Qed.

Definition contract_enforces_promises
           {S: Type}
           {I: Type -> Type}
           {State: Type}
           (requirements: forall (R: Type), I R -> S -> Prop)
           (promises: forall {R: Type} (i: I R), R -> S -> Prop)
           (abs_step: forall (R: Type), I R -> S -> S)
           (inv: S -> State -> Prop)
           (step: @PS I State)
  := forall (A: Type)
            (i: I A)
            (s: State)
            (abs: S),
    inv abs s
    -> requirements A i abs
    -> promises i (fst (step A s i)) abs.

Lemma contract_enforces_promises_propagates
      {S: Type}
      {I: Type -> Type}
      {State: Type}
      (c: Contract S I)
      (inv: S -> State -> Prop)
      (step: @PS I State)
  : forall {A: Type}
           (i: I A),
    contract_enforces_promises (requirements c) (promises c) (abstract_step c) inv step
    -> requirements c i (abstract c)
    -> contract_enforces_promises (requirements (contract_step c i))
                                  (promises (contract_step c i))
                                  (abstract_step (contract_step c i)) inv step.
Proof.
  intros A i Henf Hreq.
  unfold contract_enforces_promises in *.
  intros B i' s abs Hinv Hreq'.
  cbn.
  apply Henf.
  + exact Hinv.
  + exact Hreq'.
Qed.

Fact _stateful_contract_enforcement
     {S: Type}
     {I: Type -> Type}
     {State: Type}
     (c: Contract S I)
     (inv: S -> State -> Prop)
     (step: @PS I State)
  : forall (abs: S)
           (Hpres: contract_preserves_inv (requirements c) (abstract_step c) inv step)
           (Henf: contract_enforces_promises (requirements c) (promises c) (abstract_step c) inv step)
           (s: State),
    inv abs s
    -> Enforcer (mkInterp step s) (set_abstract c abs).
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
       apply (contract_preserves_inv_propagates inv step (set_abstract c abs) i Hpres Hreq A i abs s).
       +++ apply Hinv.
       +++ exact Hreq.
Qed.

Lemma stateful_contract_enforcement
      {I: Interface}
      {S: Type}
      {State: Type}
      (c: Contract S I)
      (inv: S -> State -> Prop)
      (step: @PS I State)
      (Hpres: contract_preserves_inv (requirements c) (abstract_step c) inv step)
      (Henf: contract_enforces_promises (requirements c) (promises c) (abstract_step c) inv step)
  : forall (s: State),
    inv (abstract c) s
    -> Enforcer (mkInterp step s) c.
Proof.
  intros s Hinv.
  cbn.
  assert (set_abstract c (abstract c) = c)
    as Heq
      by (induction c;
          reflexivity).
  rewrite <- Heq.
  apply (_stateful_contract_enforcement c inv step (abstract c) Hpres Henf s Hinv).
Qed.

Definition strongly_compliant_program
           {I: Interface}
           {A: Type}
           {Sa: Type}
           (c: Contract Sa I)
           (p: Program I A)
  := contractfull_program c p
     /\ (forall (int: Interp I),
            Enforcer int c
            -> Enforcer (execProgram int p) c).

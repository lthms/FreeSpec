Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.

Require Import FreeSpec.Program.
Require Import FreeSpec.Interp.

Record Contract
       (I: Type -> Type) :=
  { requirements {A: Type}
                 (i: I A)
    : Prop
  ; promises {A: Type}
             (i: I A)
    : typeret i -> Prop
  }.

Arguments requirements [I] (c) [A] (i).
Arguments promises [I] (c) [A] (i _).

CoInductive Enforcer
            {I: Type -> Type}
            (c: Contract I)
            (int: Interp I)
  : Prop :=
| enforced (Hprom: forall {A: Type}
                          (i: I A),
               requirements c i
               -> (promises c i) (evalInstruction int i))
           (Henf:  forall {A: Type}
                          (i: I A),
               requirements c i
               -> Enforcer c (execInstruction int i))
  : Enforcer c int.

Add Parametric Morphism
    (I: Type -> Type)
    (c: Contract I)
  : (Enforcer c)
    with signature (@interp_eq I) ==> (impl)
      as enforcer_morphism.
Proof.
  cofix.
  intros int int' Heq He.
  constructor.
  + intros A i Hreq.
    rewrite <- Heq.
    destruct He.
    apply Hprom.
    exact Hreq.
  + intros A i Hreq.
    destruct He.
    apply Henf in Hreq.
    apply (enforcer_morphism_Proper (execInstruction int i) (execInstruction int' i)) in Hreq.
    ++ exact Hreq.
    ++ destruct Heq.
       apply Hnext.
Qed.

Inductive contractfull_program
          {I: Type -> Type}
          (c: Contract I)
  : forall {A: Type}, Program I A -> Type :=
| contractfull_instr {A: Type}
                     (i: I A)
                     (Hreq: requirements c i)
  : contractfull_program c (instr i)
| contractfull_ret {A: Type}
                   (a: A)
  : contractfull_program c (ret a)
| contractfull_inv {A B: Type}
                   (p: Program I A)
                   (f: A -> Program I B)
                   (Hcp: contractfull_program c p)
                   (Hnext: forall (int: Interp I)
                                  (Henf: Enforcer c int),
                       contractfull_program c (f (evalProgram int p)))
  : contractfull_program c (bind p f).

Lemma contractfull_instr_enforcement
      {I: Type -> Type}
      {A: Type}
      {c: Contract I}
      {i: I A}
      {int: Interp I}
      (Hc: contractfull_program c (instr i))
      (Henf: Enforcer c int)
  : Enforcer c (execProgram int (instr i)).
Proof.
  destruct Henf as [Hprom Henf].
  apply (Henf A i).
  inversion Hc; simpl_existT; subst.
  exact Hreq.
Qed.

Lemma contractfull_ret_enforcement
      {I: Type -> Type}
      {A: Type}
      {c: Contract I}
      (a: A)
      {int: Interp I}
      (He: Enforcer c int)
  : Enforcer c (execProgram int (ret a)).
Proof.
  exact He.
Qed.

Lemma contractfull_program_enforcement
      {I: Type -> Type}
      {A B: Type}
      (c: Contract I)
      (p: Program I A)
  : forall (int: Interp I)
           (Hc: contractfull_program c p)
           (He: Enforcer c int),
    Enforcer c (execProgram int p).
Proof.
  induction p.
  + intros int Hc He.
    apply (contractfull_ret_enforcement a He).
  + intros int Hc He.
    apply (contractfull_instr_enforcement Hc He).
  + intros int Hc He.
    assert (contractfull_program c (f (evalProgram int p))) as Hc'.
    ++ inversion Hc; repeat simpl_existT; subst.
       apply (Hnext int He).
    ++ inversion Hc; repeat simpl_existT; subst.
       apply H with (int:=execProgram int p) in Hc'.
       exact Hc'.
       apply IHp.
       +++ exact Hcp.
       +++ exact He.
Qed.

Definition contract_preserves_inv
            {I: Type -> Type}
            {State: Type}
            (c: Contract I)
            (inv: State -> Prop)
            (step: PS State)
  := forall {A: Type}
            (i: I A)
            (s: State),
     inv s
     -> requirements c i
     -> inv (snd (step A s i)).

Definition contract_enforces_promises
            {I: Type -> Type}
            {State: Type}
            (c: Contract I)
            (inv: State -> Prop)
            (step: PS State)
  := forall {A: Type}
            (i: I A)
            (s: State),
    inv s
    -> requirements c i
    -> promises c i (fst (step A s i)).

Lemma stateful_contract_enforcement
      {I: Type -> Type}
      {State: Type}
      (c: Contract I)
      (inv: State -> Prop)
      (step: PS State)
      (Hpres: contract_preserves_inv c inv step)
      (Henf: contract_enforces_promises c inv step)
  : forall (s: State)
  , inv s
    -> Enforcer c (mkInterp step s).
Proof.
  cofix.
  intros s Hinv.
  constructor.
  + intros A i Hreq.
    apply (Henf A i s Hinv Hreq).
  + intros A i Hreq.
    apply (Hpres A i s) in Hinv.
    ++ apply (stateful_contract_enforcement (snd (step A s i)) Hinv).
    ++ exact Hreq.
Qed.

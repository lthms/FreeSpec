Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Program.Basics.

Require Import FreeSpec.Interp.
Require Import FreeSpec.Equiv.

Local Open Scope eq_scope.

Inductive Program
          (I: Type -> Type)
          (A: Type) :=
| ret (a: A)
  : Program I A
| instr (i: I A)
  : Program I A
| bind {B: Type}
       (p: Program I B)
       (f: B -> Program I A)
  : Program I A.

Arguments ret [I A] (a).
Arguments instr [I A] (i).
Arguments bind [I A B] (p f).

Fixpoint runProgram
         {I: Type -> Type}
         {A: Type}
         (int: Interp I)
         (p: Program I A)
  : (A * Interp I) :=
  match p with
  | ret a => (a, int)
  | instr i => interpret int i
  | bind p' f => runProgram (snd (runProgram int p')) (f (fst (runProgram int p')))
  end.

Definition evalProgram
           {I: Type -> Type}
           {A: Type}
           (int: Interp I)
           (p: Program I A)
  : A :=
  fst (runProgram int p).

Definition execProgram
           {I: Type -> Type}
           {A: Type}
           (int: Interp I)
           (p: Program I A)
  : Interp I :=
  snd (runProgram int p).

CoInductive program_eq
            {I: Type -> Type}
            {A: Type}
            (p: Program I A)
            (p': Program I A) :=
| program_is_eq (Hres: forall (int: Interp I),
                    evalProgram int p = evalProgram int p')
                (Hnext: forall (int: Interp I),
                    execProgram int p == execProgram int p')
  : program_eq p p'.

Lemma program_eq_refl
      {I: Type -> Type}
      {A: Type}
      (p: Program I A)
  : program_eq p p.
Proof.
  constructor; reflexivity.
Qed.

Lemma program_eq_sym
      {I: Type -> Type}
      {A: Type}
      (p p': Program I A)
  : program_eq p p'
    -> program_eq p' p.
Proof.
  intro H1.
  destruct H1 as [Hres Hnext].
  constructor.
  + intro int.
    rewrite Hres.
    reflexivity.
  + intro int.
    rewrite Hnext.
    reflexivity.
Qed.

Lemma program_eq_trans
      {I: Type -> Type}
      {A: Type}
      (p p' p'': Program I A)
  : program_eq p p'
    -> program_eq p' p''
    -> program_eq p p''.
Proof.
  intros [Hres1 Hnext1] [Hres2 Hnext2].
  constructor; intro int.
  + transitivity (evalProgram int p').
    ++ apply Hres1.
    ++ apply Hres2.
  + transitivity (execProgram int p').
    ++ apply Hnext1.
    ++ apply Hnext2.
Qed.

Add Parametric Relation
    (I: Type -> Type)
    (A: Type)
  : (Program I A) (program_eq)
    reflexivity proved by (program_eq_refl)
    symmetry proved by (program_eq_sym)
    transitivity proved by (program_eq_trans)
      as program_equiv.

Lemma interp_assoc
      {I: Type -> Type}
      {A B C: Type}
      (p: Program I A)
      (f: A -> Program I B)
      (g: B -> Program I C)
  : program_eq (bind (bind p f) g) (bind p (fun x => bind (f x) g)).
Proof.
  constructor.
  + reflexivity.
  + reflexivity.
Qed.

Lemma interp_assoc2
           {I: Type -> Type}
           {A B: Type}
           (int: Interp I)
           (p: Program I A)
           (f: A -> Program I B)
  : runProgram int (bind p f)
    == runProgram (execProgram int p) (f (evalProgram int p)).
Proof.
  reflexivity.
Qed.

Add Parametric Morphism
    (I: Type -> Type)
    (A: Type)
  : (runProgram)
    with signature eq ==> (program_eq) ==> (@run_interp_eq I A)
  as run_program_morphism.
Proof.
  intros y p p' Heq.
  constructor.
  destruct Heq.
  + apply Hres.
  + apply Heq.
Qed.

Add Parametric Morphism
    (I: Type -> Type)
    (A: Type)
  : (evalProgram)
    with signature eq ==> (@program_eq I A) ==> (eq)
  as eval_program_morphism.
Proof.
  intros y p p' Heq.
  unfold evalProgram.
  rewrite Heq.
  reflexivity.
Qed.

Add Parametric Morphism
    (I: Type -> Type)
    (A: Type)
  : (execProgram)
    with signature eq ==> (@program_eq I A) ==> (@interp_eq I)
  as exec_program_morphism.
Proof.
  intros y p p' Heq.
  unfold execProgram.
  rewrite Heq.
  reflexivity.
Qed.

Definition typeret
           {I: Type -> Type}
           {A: Type}
           (i: I A)
  : Type := A.

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

Definition PS
           {I: Type -> Type}
           (State: Type)
  := forall {A: Type}, State -> I A -> (A * State).

CoFixpoint mkInterp
           {I: Type -> Type}
           {State: Type}
           (ps: PS State)
           (s: State)
  : Interp I :=
  interp (
      fun (A: Type)
          (p: I A) =>
        (fst  (ps A s p), mkInterp ps (snd (ps A s p)))).

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

Notation "p >>= f" := (bind p f) (at level 50) : prog_scope.
Notation "a <- p ; q" :=
  (bind p (fun a => q)) (at level 60, right associativity, p at next level)
  : prog_scope.
Notation "[ i ]" := (instr i) (at level 50) : prog_scope.
Notation "· a" := (ret a) (at level 50) : prog_scope.
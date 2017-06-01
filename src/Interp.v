Require Import Coq.Classes.Equivalence.
Require Import Coq.Setoids.Setoid.

Require Import FreeSpec.Tuple.
Require Import FreeSpec.Equiv.

Local Open Scope eq_scope.

CoInductive Interp
            (I: Type -> Type)
  : Type :=
| interp (f: forall {A: Type}, I A -> (A * Interp I))
  : Interp I.

Arguments interp [I] (f).

Definition interpret
           {I: Type -> Type}
           {A: Type}
           (int: Interp I)
           (i: I A)
  : (A * Interp I) :=
  match int with interp f => f A i end.

Definition evalInstruction
           {I: Type -> Type}
           {A: Type}
           (int: Interp I)
           (i: I A)
  : A :=
  fst (interpret int i).

Definition execInstruction
           {I: Type -> Type}
           {A: Type}
           (int: Interp I)
           (i: I A)
    : Interp I :=
    snd (interpret int i).

CoInductive interp_eq
            {I: Type -> Type}
            (int1: Interp I)
            (int2: Interp I)
  : Prop :=
| interp_is_eq (Hres: forall {A: Type}
                             (i: I A),
                   evalInstruction int1 i = evalInstruction int2 i)
               (Hnext: forall {A: Type}
                              (i: I A),
                   interp_eq (execInstruction int1 i) (execInstruction int2 i))
  : interp_eq int1 int2.

Lemma interp_eq_refl
      {I: Type -> Type}
  : forall (int: Interp I),
    interp_eq int int.
Proof.
  cofix.
  intros int.
  constructor.
  + reflexivity.
  + intros A i.
    apply interp_eq_refl.
Qed.

Lemma interp_eq_sym
      {I: Type -> Type}
  : forall (int int': Interp I),
    interp_eq int int'
    -> interp_eq int' int.
Proof.
  cofix.
  intros int int' H1.
  destruct H1.
  constructor.
  + intros A i.
    symmetry.
    exact (Hres A i).
  + intros A i.
    apply (interp_eq_sym (snd (interpret int i)) (snd (interpret int' i)) (Hnext A i)).
Qed.

Lemma interp_eq_trans
      {I: Type -> Type}
  : forall (int int' int'': Interp I),
    interp_eq int int'
    -> interp_eq int' int''
    -> interp_eq int int''.
Proof.
  cofix.
  intros int int' int'' H1 H2.
  destruct H1 as [Hres1 Hnext1].
  destruct H2 as [Hres2 Hnext2].
  constructor.
  + intros A i.
    transitivity (fst (interpret int' i)).
    exact (Hres1 A i).
    exact (Hres2 A i).
  + intros A i.
    apply (interp_eq_trans (snd (interpret int i))
                           (snd (interpret int' i))
                           (snd (interpret int'' i))
                           (Hnext1 A i)
                           (Hnext2 A i)).
Qed.

Add Parametric Relation
    (I: Type -> Type)
  : (Interp I) (@interp_eq I)
  reflexivity proved by (@interp_eq_refl I)
  symmetry proved by (@interp_eq_sym I)
  transitivity proved by (@interp_eq_trans I)
    as interp_rel.

Instance eqInterp (I: Type -> Type): Eq (Interp I) :=
  {| equiv := @interp_eq I |}.

Definition run_interp_eq
           {I: Type -> Type}
           {A: Type}
           (o o': (A * Interp I))
  : Prop :=
  fst o = fst o' /\ snd o == snd o'.

Lemma run_interp_eq_refl
           {I: Type -> Type}
           {A: Type}
           (o: (A * Interp I))
  : run_interp_eq o o.
Proof.
  constructor; reflexivity.
Qed.

Lemma run_interp_eq_sym
           {I: Type -> Type}
           {A: Type}
           (o o': (A * Interp I))
  : run_interp_eq o o'
    -> run_interp_eq o' o.
Proof.
  intros [H H']; symmetry in H; symmetry in H'.
  constructor; [exact H|exact H'].
Qed.

Lemma run_interp_eq_trans
           {I: Type -> Type}
           {A: Type}
           (o o' o'': (A * Interp I))
  : run_interp_eq o o'
    -> run_interp_eq o' o''
    -> run_interp_eq o o''.
Proof.
  intros [H H'] [G G'].
  constructor.
  + rewrite H; exact G.
  + rewrite H'; exact G'.
Qed.

Add Parametric Relation
    (I: Type -> Type)
    (A: Type)
  : (A * Interp I) (@run_interp_eq I A)
    reflexivity proved by (run_interp_eq_refl)
    symmetry proved by (run_interp_eq_sym)
    transitivity proved by (run_interp_eq_trans)
      as run_interp_equiv.

Add Parametric Morphism
    (I: Type -> Type)
    (A: Type)
  : (@fst A (Interp I))
    with signature (run_interp_eq) ==> (@eq A)
  as fst_program_morphism.
Proof.
  intros o o' [H _H].
  exact H.
Qed.

Add Parametric Morphism
    (I: Type -> Type)
    (A: Type)
  : (@snd A (Interp I))
    with signature (run_interp_eq) ==> (interp_eq)
  as snd_program_morphism.
Proof.
  intros o o' [_H H].
  exact H.
Qed.

Instance eq_run_interp
         {I: Type -> Type}
         {A: Type}
  : Eq (A * Interp I) :=
  {| equiv := run_interp_eq |}.

Add Parametric Morphism
    (I: Type -> Type)
    (A: Type)
  : (interpret)
    with signature (@interp_eq I) ==> (@eq (I A)) ==> (run_interp_eq)
      as interp_int_morphism.
Proof.
  intros int int' Heq i.
  constructor.
  + destruct Heq.
    apply (Hres A i).
  + destruct Heq.
    assert (interp_eq (snd (interpret int i)) (snd (interpret int' i)))
      as Hin
        by (apply Hnext).
    apply Hnext.
Qed.

Add Parametric Morphism
    (I: Type -> Type)
    (A: Type)
  : (evalInstruction)
    with signature (@interp_eq I) ==> (@eq (I A)) ==> (eq)
      as eval_instr_morphism.
Proof.
  intros int int' Heq i.
  unfold evalInstruction.
  rewrite Heq.
  reflexivity.
Qed.

Add Parametric Morphism
    (I: Type -> Type)
    (A: Type)
  : (execInstruction)
    with signature (@interp_eq I) ==> (@eq (I A)) ==> (@interp_eq I)
      as exec_instr_morphism.
Proof.
  intros int int' Heq i.
  unfold execInstruction.
  rewrite Heq.
  reflexivity.
Qed.

(* A list of goal to check the rewrite tactic actually works *)

Goal (forall (I: Type -> Type)
             (int int': Interp I)
             (A: Type)
             (eqA: Eq A)
             (i: I A),
         int == int'
         -> evalInstruction int i == evalInstruction int' i).
Proof.
  intros I int int' A eqA i Heq.
  rewrite Heq.
  reflexivity.
Qed.

Goal (forall (I: Type -> Type)
             (int int': Interp I)
             (A: Type)
             (eqA: Eq A)
             (i: I A),
         int == int'
         -> execInstruction int i == execInstruction int' i).
Proof.
  intros I int int' A eqA i Heq.
  rewrite Heq.
  reflexivity.
Qed.
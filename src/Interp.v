Require Import Coq.Classes.Equivalence.
Require Import Coq.Setoids.Setoid.

Require Import FreeSpec.Tuple.
Require Import FreeSpec.Equiv.

Local Open Scope eq_scope.

Section INTERP.
  Variable (Instruction: Type -> Type).

  CoInductive Interp: Type :=
  | interp (f: forall {A: Type}, Instruction A -> (A * Interp))
    : Interp.

  Definition interpret
             {A: Type}
             (i: Instruction A)
             (int: Interp)
    : (A * Interp) :=
    match int with interp f => f A i end.

  Definition evalInstruction
             {A: Type}
             (i: Instruction A)
             (int: Interp)
    : A :=
    fst (interpret i int).

  Definition execInstruction
             {A: Type}
             (i: Instruction A)
             (int: Interp)
    : Interp :=
    snd (interpret i int).

  CoInductive interp_eq
              (i1: Interp)
              (i2: Interp)
    : Prop :=
  | interp_is_eq (Hres: forall {A: Type}
                              `{Eq A}
                               (i: Instruction A),
                     evalInstruction i i1 == evalInstruction i i2)
                 (Hnext: forall {A: Type}
                                (i: Instruction A),
                     interp_eq (execInstruction i i1) (execInstruction i i2))
    : interp_eq i1 i2.

  Lemma interp_eq_refl
    : forall (i: Interp), interp_eq i i.
  Proof.
    cofix.
    intro i.
    constructor.
    + reflexivity.
    + intros A p.
      apply interp_eq_refl.
  Qed.

  Lemma interp_eq_sym
    : forall (i i': Interp), interp_eq i i' -> interp_eq i' i.
  Proof.
    cofix.
    intros int int' H1.
    destruct H1.
    constructor.
    + intros A eqA i.
      symmetry.
      exact (Hres A eqA i).
    + intros A i.
      apply (interp_eq_sym (snd (interpret i int)) (snd (interpret i int')) (Hnext A i)).
  Qed.

  Lemma interp_eq_trans
    : forall (i i' i'': Interp),
      interp_eq i i'
      -> interp_eq i' i''
      -> interp_eq i i''.
  Proof.
    cofix.
    intros i i' i'' H1 H2.
    destruct H1 as [Hres1 Hnext1].
    destruct H2 as [Hres2 Hnext2].
    constructor.
    + intros A eqA p.
      transitivity (fst (interpret p i')).
      exact (Hres1 A eqA p).
      exact (Hres2 A eqA p).
    + intros A p.
      apply (interp_eq_trans (snd (interpret p i))
                             (snd (interpret p i'))
                             (snd (interpret p i''))
                             (Hnext1 A p)
                             (Hnext2 A p)).
  Qed.
End INTERP.

Arguments interp [_].
Arguments interp_eq [_].
Arguments interpret [_ _].
Arguments evalInstruction [_ _].
Arguments execInstruction [_ _].
Arguments interp_eq_refl [_].
Arguments interp_eq_sym [_].
Arguments interp_eq_trans [_].

Add Parametric Relation
    (I: Type -> Type)
  : (Interp I) (@interp_eq I)
  reflexivity proved by (@interp_eq_refl I)
  symmetry proved by (@interp_eq_sym I)
  transitivity proved by (@interp_eq_trans I)
    as interp_rel.

Instance eqInterp (I: Type -> Type): Eq (Interp I) :=
  {| equiv := @interp_eq I |}.

Local Open Scope eq_scope.

Lemma _interp_int_morphism
  : forall (I: Type -> Type)
           (x y : Interp I)
           (A: Type)
           {eqA: Eq A}
           (i: I A),
  x == y -> (interpret i x) == (interpret i y).
Proof.
  intros I int int' A eqA i Heq.
  constructor.
  + destruct Heq.
    apply (Hres A eqA i).
  + destruct Heq.
    assert (interp_eq (snd (interpret i int)) (snd (interpret i int')))
      as Hin
        by (apply Hnext).
    apply Hnext.
Qed.

Add Parametric Morphism
    (I: Type -> Type)
    (A: Type)
    (eqA: Eq A)
    (i: I A)
  : (interpret i)
    with signature (@interp_eq I) ==> (@tuple_eq A (Interp I) eqA (eqInterp I))
      as interp_int_morphism.
Proof.
  intros int int' Heq.
  constructor.
  + destruct Heq.
    apply (Hres A eqA i).
  + destruct Heq.
    assert (interp_eq (snd (interpret i int)) (snd (interpret i int'))).
    apply (Hnext A i).
    rewrite H.
    reflexivity.
Qed.

Add Parametric Morphism
    (I: Type -> Type)
    (A: Type)
    (eqA: Eq A)
    (i: I A)
  : (evalInstruction i)
    with signature (@interp_eq I) ==> (@equiv A eqA)
      as eval_instr_morphism.
Proof.
  apply interp_int_morphism.
Qed.

Add Parametric Morphism
    (I: Type -> Type)
    (A: Type)
    (eqA: Eq A)
    (i: I A)
  : (execInstruction i)
    with signature (@interp_eq I) ==> (@interp_eq I)
      as exec_instr_morphism.
Proof.
  apply interp_int_morphism.
  exact eqA.
Qed.

(* A list of goal to check the rewrite tactic actually works *)

Goal (forall (I: Type -> Type)
             (int int': Interp I)
             (A: Type)
             (eqA: Eq A)
             (i: I A),
         int == int'
         -> evalInstruction i int == evalInstruction i int').
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
         -> execInstruction i int == execInstruction i int').
Proof.
  intros I int int' A eqA i Heq.
  rewrite Heq.
  reflexivity.
Qed.
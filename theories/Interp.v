(*begin hide *)
Require Import Coq.Classes.Equivalence.
Require Import Coq.Setoids.Setoid.
(* end hide *)

Require Export FreeSpec.Interface.
Require Import FreeSpec.WEq.

Local Open Scope free_weq_scope.

(** * [Interp]reter

    In a nutshell, an Interpreter is function which takes an
    instruction of a given [Interface] and returns both a result and a
    new Interpreter. This choice of model has been made to abstract
    away how a Interpreter is implemented. A stateless Interpreter
    will simply returns itself when a stateful one will carry a state,
    yet both can be use rigourously the same way.

    Therefore, an Interpreter is defined as a coinductive type
    [Interp] and is provided along with [interpret], a function to
    actually performs the interpretation. Because an Interpreter
    returns a tuple, a type which is not always great to work with, we
    provide [evalInstruction] and [execInstruction] as
    shortcuts. Their naming follows the same logic as the Haskell
    state monad functions.

 *)

CoInductive Interp
            (I: Interface)
  : Type :=
| interp (f: forall {A: Type}, I A -> (A * Interp I))
  : Interp I.

Arguments interp [I] (f).

Definition interpret
           {I:   Interface}
           {A:   Type}
           (int: Interp I)
           (i:   I A)
  : (A * Interp I) :=
  match int with interp f => f A i end.

Definition evalInstruction
           {I:   Interface}
           {A:   Type}
           (int: Interp I)
           (i:   I A)
  : A :=
  fst (interpret int i).

Definition execInstruction
           {I:   Interface}
           {A:   Type}
           (int: Interp I)
           (i:   I A)
    : Interp I :=
    snd (interpret int i).

(** ** Interpreters Equivalence

    Two Interpreters are said to be equivalent when they always return
    the exact same result and when their resulting Interpreters are
    equivalent themselves.

 *)

CoInductive interp_eq
            {I:    Interface}
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

(** It is possible to prove [interp_eq] is effectively an equivalence.

 *)

Lemma interp_eq_refl
      {I: Interface}
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
      {I: Interface}
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
      {I: Interface}
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
    (I: Interface)
  : (Interp I) (interp_eq)
  reflexivity  proved by (interp_eq_refl)
  symmetry     proved by (interp_eq_sym)
  transitivity proved by (interp_eq_trans)
    as interp_rel.

Instance interp_eq_eq
         (I: Interface)
  : WEq (Interp I) :=
  {| weq := @interp_eq I |}.

(** ** Interpretation Result WEquivalence

    To help Coq when it comes to generalized rewriting, we define an
    equivalence relation for the result of an interpretation, along
    with several morphisms.
 *)

Definition run_interp_eq
           {I:    Interface}
           {A:    Type}
           (o o': (A * Interp I))
  : Prop :=
  fst o = fst o' /\ snd o == snd o'.

Lemma run_interp_eq_refl
           {I: Interface}
           {A: Type}
           (o: (A * Interp I))
  : run_interp_eq o o.
Proof.
  constructor; reflexivity.
Qed.

Lemma run_interp_eq_sym
           {I:   Interface}
           {A:   Type}
           (x y: (A * Interp I))
  : run_interp_eq x y
    -> run_interp_eq y x.
Proof.
  intros [H H']; symmetry in H; symmetry in H'.
  constructor; [exact H|exact H'].
Qed.

Lemma run_interp_eq_trans
           {I:     Interface}
           {A:     Type}
           (x y z: (A * Interp I))
  : run_interp_eq x y
    -> run_interp_eq y z
    -> run_interp_eq x z.
Proof.
  intros [H H'] [G G'].
  constructor.
  + rewrite H; exact G.
  + rewrite H'; exact G'.
Qed.

Add Parametric Relation
    (I: Interface)
    (A: Type)
  : (A * Interp I) (@run_interp_eq I A)
    reflexivity  proved by (run_interp_eq_refl)
    symmetry     proved by (run_interp_eq_sym)
    transitivity proved by (run_interp_eq_trans)
      as run_interp_equiv.

Instance eq_run_interp
         {I: Interface}
         {A: Type}
  : WEq (A * Interp I) :=
  { weq := run_interp_eq
  }.

(** We then provide the required morphisms for one to be able to
    rewrite terms using the [run_interp_eq] equivalence relation.

 *)

Add Parametric Morphism
    (I: Interface)
    (A: Type)
  : (@fst A (Interp I))
    with signature (run_interp_eq) ==> (@eq A)
  as fst_program_morphism.
Proof.
  intros o o' [H _H].
  exact H.
Qed.

Add Parametric Morphism
    (I: Interface)
    (A: Type)
  : (@snd A (Interp I))
    with signature (run_interp_eq) ==> (interp_eq)
  as snd_program_morphism.
Proof.
  intros o o' [_H H].
  exact H.
Qed.

Add Parametric Morphism
    (I: Interface)
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
    (I: Interface)
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
    (I: Interface)
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

(* begin hide *)

(* A list of goal to check the rewrite tactic actually works *)

Goal (forall (I:        Interface)
             (int int': Interp I)
             (A:        Type)
             (eqA:      WEq A)
             (i:        I A),
         int == int'
         -> evalInstruction int i == evalInstruction int' i).
Proof.
  intros I int int' A eqA i Heq.
  rewrite Heq.
  reflexivity.
Qed.

Goal (forall (I:        Interface)
             (int int': Interp I)
             (A:        Type)
             (eqA:      WEq A)
             (i:        I A),
         int == int'
         -> execInstruction int i == execInstruction int' i).
Proof.
  intros I int int' A eqA i Heq.
  rewrite Heq.
  reflexivity.
Qed.
(* end hide *)

(** * Stateful Interpreter

    The function [mkInterp] is here to ease the definition of new
    so-called stateful interpreters. More precisely, it turns a
    function which, given an internal state and an instruction to
    interpret, returns a new state and the instruction
    result. [mkInterp] wraps this function to make it an [Interp].

 *)

Definition PS
           {I:     Interface}
           (State: Type)
  := forall (A: Type), State -> I A -> (A * State).

CoFixpoint mkInterp
           {I:     Interface}
           {State: Type}
           (ps:    PS State)
           (s:     State)
  : Interp I :=
  interp (
      fun (A: Type)
          (p: I A) =>
        (fst  (ps A s p), mkInterp ps (snd (ps A s p)))).

(** * Interpreters for Labeled Instructions

    We can enrich an Interpreter to interpret label Instruction. It
    will just ignore the labels, which is basically what we
    want. However, when we will define contracts for our Interfaces,
    we can use the label to give a more precise definition based on
    usage context.

    *)

Local Open Scope free_scope.

Definition enrich_interpreter
           {I:   Interface}
           (L:   Type)
           (int: Interp I)
  : Interp (I <?> L) :=
  mkInterp (fun (A: Type)
                (int: Interp I)
                (i: (I <?> L) A)
            => match i with
               | i <:> _
                 => interpret int i
               end)
           int.
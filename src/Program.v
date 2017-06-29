Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Program.Basics.

Require Import FreeSpec.Interp.
Require Import FreeSpec.Equiv.

Local Open Scope eq_scope.

(** * The [Program] Monad

    In this section, we introduce the [Program] Monad. Its definition
    is inspired by the Haskell #<a
    href="https://hackage.haskell.org/package/operational">#operational#</a>#
    package.  Thanks to the [Program] Monad, it becomes easy to
    specify complex computations upon a given set of instructions.

    To realize a given computation, the [runProgram] function is
    provided. This functions takes an [Interp] in addition to a
    [Program] and returns the result of the computation along with a
    new interpreter. Two helpers functions ([evalProgram] and
    [execProgram]) are provided.

 *)

(** ** Definition

    Given [I] a set of instructions (that is, of kind [Interface])
    and [A] the type of the result of a given computation, the type of
    this computation specification is [Program I A].

    Under the hood, a [Program] is an AST to wrap and chain several
    call to an underlying interface. More precisely, a [Program] can
    be:

    - [ret a], a pure value
    - [instr i], a call to the underlying interface through the
      instruction [i]
    - [bind p f], a first computation whose result determines the
      following computation to execute

 *)

Inductive Program
          (I: Interface)
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

(** ** Execution

    To actually perform a computation [Program I A], one needs a
    corresponding interpreter [Interp I] for the interface described
    by [I].

 *)

Fixpoint runProgram
         {I: Interface}
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
           {I: Interface}
           {A: Type}
           (int: Interp I)
           (p: Program I A)
  : A :=
  fst (runProgram int p).

Definition execProgram
           {I: Interface}
           {A: Type}
           (int: Interp I)
           (p: Program I A)
  : Interp I :=
  snd (runProgram int p).

(** ** [Program]s Equivalence

    Two [Program] are equivalent when they always gives both the exact
    same result and two equivalent interpreter (according to
    [interp_eq]), no matter the input interpreter.

 *)

CoInductive program_eq
            {I: Interface}
            {A: Type}
            (p: Program I A)
            (p': Program I A) :=
| program_is_eq (Hres: forall (int: Interp I),
                    evalProgram int p = evalProgram int p')
(*
  TODO: Do we really need the interpreter equivalence? maybe the
  simple equality is enough
 *)
                (Hnext: forall (int: Interp I),
                    execProgram int p == execProgram int p')
  : program_eq p p'.

(**
    We can easily prove this property is indeed and equivalence by
    showing it is reflexive, symmetric and transitive.

 *)

Lemma program_eq_refl
      {I: Interface}
      {A: Type}
      (p: Program I A)
  : program_eq p p.
Proof.
  constructor; reflexivity.
Qed.

Lemma program_eq_sym
      {I: Interface}
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
      {I: Interface}
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
    (I: Interface)
    (A: Type)
  : (Program I A) (program_eq)
    reflexivity proved by (program_eq_refl)
    symmetry proved by (program_eq_sym)
    transitivity proved by (program_eq_trans)
      as program_equiv.

(** Also, we can easily show the [program_eq] property is strong
    enough to be used to replace two equivalent programs in several
    cases.

 *)

Add Parametric Morphism
    (I: Interface)
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
    (I: Interface)
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
    (I: Interface)
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

Instance program_eq_eq
         (I: Interface)
         (A: Type)
  : Eq (Program I A) :=
  {| equiv := program_eq |}.

(** ** Monad Laws

    [Program] _is_ a Monad and therefore obeys the Monad laws.  The
    #<a href="https://wiki.haskell.org/Monad_laws">#Haskell Wiki#</a>#
    explains in depth what are the laws and why they are usefull. In a
    nutshell, the laws are intended to ease the use of a given Monad
    by a programmer by making the monad functionning in general more
    predictible. By conforming to the Monad laws, one knows its monad
    will have more chance to behave the way its users may expect it
    to.

    Fortunately, in our case, proving the Monad laws is straightforward.

 *)

Fact program_left_identity
     {I: Interface}
     {A B: Type}
     (a: A)
     (f: A -> Program I B)
  : program_eq (bind (ret a) f) (f a).
Proof.
  constructor.
  + reflexivity.
  + reflexivity.
Qed.

Fact program_right_identity
     {I: Interface}
     {A: Type}
     (p: Program I A)
  : program_eq (bind p (@ret I A)) p.
Proof.
  constructor.
  + reflexivity.
  + reflexivity.
Qed.

Fact program_associativity
     {I: Interface}
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

(** ** Alternative [Program] Execution

    We provide the function [runProgram'] as a probably more efficient
    way to run a given Program. The difference is actually quite
    simple: [runProgram] makes no use of the [let ... in] feature
    because our tests have shown Coq sometimes have some trouble
    dealing with this construction. As a consequence, some calls are
    made twice or even more.

    Thanks to the [run_program_equiv] lemma, one can use [runProgram]
    for her proofs and extract [runProgram'].

 *)
Fixpoint runProgram'
         {I: Interface}
         {A: Type}
         (int: Interp I)
         (p: Program I A)
  : (A * Interp I) :=
  match p with
  | ret a => (a, int)
  | instr i => interpret int i
  | bind p' f => let o := runProgram int p'
                 in runProgram (snd o) (f (fst o))
  end.

Lemma run_program_equiv
      {I: Interface}
      {A: Type}
      (int: Interp I)
      (p: Program I A)
  : runProgram int p = runProgram' int p.
Proof.
  induction p; reflexivity.
Qed.

(** ** Notations

 *)

Notation "p >>= f" := (bind p f) (at level 50) : prog_scope.
Notation "a <- p ; q" :=
  (bind p (fun a => q)) (at level 60, right associativity, p at next level)
  : prog_scope.
Notation "p ;; q" :=
  (bind p (fun _ => q)) (at level 60, right associativity)
  : prog_scope.
Notation "[ i ]" := (instr i) (at level 50) : prog_scope.
Notation "· a" := (ret a) (at level 50) : prog_scope.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Setoids.Setoid.

Require Import FreeSpec.Equiv.

Local Open Scope eq_scope.

Section TUPLE_EQUIV.

  Context {A B: Type}
         `{Eq A}
         `{Eq B}.

  Definition tuple_eq
             (t t': (A * B))
    : Prop :=
    (fst t) == (fst t') /\
    (snd t) == (snd t').

  Lemma tuple_eq_refl
        (t: (A * B))
    : tuple_eq t t.
  Proof.
    constructor; reflexivity.
  Qed.

  Lemma tuple_eq_sym
        (t t': (A * B))
    : tuple_eq t t' -> tuple_eq t' t.
  Proof.
    intros [Hfst Hsnd].
    constructor; symmetry; [ exact Hfst | exact Hsnd ].
  Qed.

  Lemma tuple_eq_trans
        (t t' t'': (A * B))
    : tuple_eq t t'
      -> tuple_eq t' t''
      -> tuple_eq t t''.
  Proof.
    intros [Hfst Hsnd] [Hfst' Hsnd'].
    constructor; [ transitivity (fst t') | transitivity (snd t') ]; assumption.
  Qed.
End TUPLE_EQUIV.

Add Parametric Relation
    (A B: Type)
    (eqA: Eq A)
    (eqB: Eq B)
  : (A * B) (@tuple_eq A B eqA eqB)
    reflexivity proved by (@tuple_eq_refl A B eqA eqB)
    symmetry proved by (@tuple_eq_sym A B eqA eqB)
    transitivity proved by (@tuple_eq_trans A B eqA eqB)
      as tuple_rel.

Add Parametric Morphism
    (A B: Type)
    (eqA: Eq A)
    (eqB: Eq B)
    (b: B)
  : (fun a => (a, b))
    with signature (@equiv A eqA) ==> (@tuple_eq A B eqA eqB)
      as pure_a_morph.
Proof.
  intros x y Heq.
  constructor.
  + exact Heq.
  + reflexivity.
Qed.

Add Parametric Morphism
    (A B: Type)
    (eqA: Eq A)
    (eqB: Eq B)
    (a: A)
  : (fun (b: B) => (a, b))
    with signature (@equiv B eqB) ==> (@tuple_eq A B eqA eqB)
      as pure_b_morph.
Proof.
  intros x y Heq.
  constructor.
  + reflexivity.
  + exact Heq.
Qed.

Add Parametric Morphism
    (A B: Type)
    (eqA: Eq A)
    (eqB: Eq B)
  : (fst)
    with signature  (@tuple_eq A B eqA eqB) ==> (@equiv A eqA)
      as fst_morph.
Proof.
  intros x y [Heq _H].
  exact Heq.
Qed.

Add Parametric Morphism
    (A B: Type)
    (eqA: Eq A)
    (eqB: Eq B)
  : (snd)
    with signature  (@tuple_eq A B eqA eqB) ==> (@equiv B eqB)
      as snd_morph.
Proof.
  intros x y [_H Heq].
  exact Heq.
Qed.

Instance tupleEq
         (A B: Type)
         `{Eq A}
         `{Eq B}
  : Eq (A * B) :=
  { equiv := tuple_eq
  }.
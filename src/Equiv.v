Require Import Coq.Classes.Equivalence.
Require Import Coq.Setoids.Setoid.

Class Eq (A: Type) :=
  { equiv: A -> A -> Prop
  ; rel: Equivalence equiv
  }.

Arguments equiv [A _] (_ _).

Class EqDec
      (A: Type)
     `{Eq A} :=
  { equiv_dec: forall (a a': A), {equiv a a'}+{~equiv a a'}
  }.

Arguments equiv_dec [A _ _] (_ _).

Notation "a == b" := (equiv a b) (at level 70, no associativity) : eq_scope.
Notation "a /= b" := (~ equiv a b) (at level 70, no associativity) : eq_scope.
Notation "a =? b" := (equiv_dec a b) (at level 70, no associativity) : eq_scope.
Local Open Scope eq_scope.

Lemma eq_refl
      {A: Type}
     `{Eq A}
      (a: A)
  : a == a.
Proof.
  destruct H.
  reflexivity.
Qed.

Lemma eq_sym
      {A: Type}
     `{Eq A}
      (a a': A)
  : a == a' -> a' == a.
Proof.
  destruct H.
  intro H.
  symmetry.
  exact H.
Qed.

Lemma eq_trans
      {A: Type}
     `{Eq A}
      (a a' a'': A)
  : a == a' -> a' == a'' -> a == a''.
Proof.
  destruct H.
  intros H H'.
  transitivity (a'); assumption.
Qed.

Add Parametric Relation
    (A: Type)
    (eqA: Eq A)
  : (A) (@equiv A eqA)
    reflexivity proved by (@eq_refl A eqA)
    symmetry proved by (@eq_sym A eqA)
    transitivity proved by (@eq_trans A eqA)
      as eq_rel.
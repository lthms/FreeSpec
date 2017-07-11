Require Import Coq.Classes.Equivalence.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Bool.Bool.

Require Import FreeSpec.PropBool.

(** * Weaker Equality

    For a number of type, the Coq equality is too strong. Therefore,
    we introduce the idea of a _weaker equality_ one can use in place
    of the Leibniz equality used in Coq.

 *)

Class WEq
      (A: Type) :=
  { weq (a a': A): Prop
  ; rel:> Equivalence weq
  }.

Arguments weq [A _] (_ _).

Infix "==" :=
  weq
    (at level 70, no associativity)
  : free_weq_scope.

Notation "a /= b" :=
  (~ weq a b)
    (at level 70, no associativity)
  : free_weq_scope.

(** * Weaker Decidable Equality

    Sometimes, it is not enough to have an equality. Thus, we
    introduce the notion of weaker decidable equality. It comes in two
    “flavors”: one based on sumbool and one based on bool.

 *)

Class WEqDec
      (A: Type)
     `{WEq A} :=
  { weq_dec (a a': A): {weq a a'} + {~weq a a'}
  }.

Arguments weq_dec [A _ _] (_ _).

Infix "=?" :=
  weq_dec
    (at level 70, no associativity)
  : free_weq_scope.

Class WEqBool
      (A: Type)
     `{WEq A} :=
  { weq_bool (a a': A): bool
  ; weq_bool_is_bool_prop :> PropBool2 (@weq A _) weq_bool
  }.

Arguments weq_bool [A _ _] (_ _).

Lemma weq_bool_weq
      {A:    Type}
     `{WEqBool A}
      (a a': A)
  : weq_bool a a' = true <-> weq a a'.
Proof.
  apply pred_bool_pred_2.
Qed.

Lemma weq_bool_refl
      {A: Type}
     `{WEqBool A}
      (a: A)
  : weq_bool a a = true.
Proof.
  apply weq_bool_weq.
  reflexivity.
Qed.

Lemma weq_bool_false
      {A:    Type}
     `{WEqBool A}
      (a a': A)
  : weq_bool a a' = false <-> ~weq a a'.
Proof.
  split.
  + intros Hweq_bool Hweq.
    apply (weq_bool_weq a a') in Hweq.
    rewrite Hweq in Hweq_bool.
    discriminate.
  + intros Hnweq.
    case_eq (weq_bool a a'); intro Heq.
    ++ apply weq_bool_weq in Heq.
       apply Hnweq in Heq.
       destruct Heq.
    ++ reflexivity.
Qed.

Infix "?=" :=
  weq_bool
    (at level 70, no associativity)
  : free_weq_scope.
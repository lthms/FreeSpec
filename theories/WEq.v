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

Local Open Scope free_weq_scope.

(** ** Function Instances

 *)

Definition function_weq
           {a b: Type}
          `{WEq b}
           (f g: a -> b)
  : Prop :=
  forall (x: a), f x == g x.

Lemma function_weq_refl
      {a b: Type}
     `{WEq b}
      (f: a -> b)
  : function_weq f f.
Proof.
  intro x.
  reflexivity.
Qed.

Lemma function_weq_sym
      {a b: Type}
     `{WEq b}
      (f g: a -> b)
  : function_weq f g
    -> function_weq g f.
Proof.
  unfold function_weq.
  intros H' x.
  rewrite H'.
  reflexivity.
Qed.

Lemma function_weq_trans
      {a b: Type}
     `{WEq b}
      (f g h: a -> b)
  : function_weq f g
    -> function_weq g h
    -> function_weq f h.
Proof.
  unfold function_weq.
  intros F G x.
  rewrite <- (G x).
  exact (F x).
Qed.

Add Parametric Relation
    (a b: Type)
   `{WEq b}
  : (a -> b) (function_weq)
    reflexivity  proved by function_weq_refl
    symmetry     proved by function_weq_sym
    transitivity proved by function_weq_trans
      as function_web_equiv.

Instance function_WEq
         (a b: Type)
        `{WEq b}
  : WEq (a -> b) :=
  { weq := function_weq
  }.

(** ** Tuple Instances

 *)

Definition tuple_weq
           {a b: Type}
          `{WEq a}
          `{WEq b}
           (o o': a * b)
  : Prop :=
  fst o == fst o' /\ snd o == snd o'.

Lemma tuple_weq_refl
      {a b: Type}
     `{WEq a}
     `{WEq b}
      (o: a * b)
  : tuple_weq o o.
Proof.
  split; reflexivity.
Qed.

Lemma tuple_weq_sym
      {a b: Type}
     `{WEq a}
     `{WEq b}
      (o o': a * b)
  : tuple_weq o o'
    -> tuple_weq o' o.
Proof.
  intros [Hf Hs].
  split; [ rewrite Hf; reflexivity
         | rewrite Hs; reflexivity
         ].
Qed.

Lemma tuple_weq_trans
      {a b: Type}
     `{WEq a}
     `{WEq b}
      (o o' o'': a * b)
  : tuple_weq o o'
    -> tuple_weq o' o''
    -> tuple_weq o o''.
Proof.
  intros [Of Os] [Of' Os'].
  split; [ rewrite Of; exact Of'
         | rewrite Os; exact Os'
         ].
Qed.

Add Parametric Relation
    (a b: Type)
   `{WEq a}
   `{WEq b}
  : (a * b) (tuple_weq)
    reflexivity  proved by tuple_weq_refl
    symmetry     proved by tuple_weq_sym
    transitivity proved by tuple_weq_trans
      as tuple_weq_equiv.

Instance tuple_WEq
         (a b: Type)
        `{WEq a}
        `{WEq b}
  : WEq (a * b) :=
  { weq := tuple_weq
  }.

Add Parametric Morphism
    (a b: Type)
   `{WEq a}
   `{WEq b}
  : fst
    with signature (@weq (a * b) _) ==> (@weq a _)
      as fst_tuple_weq_morphism.
Proof.
  intros o o' [P Q].
  exact P.
Qed.

Add Parametric Morphism
    (a b: Type)
   `{WEq a}
   `{WEq b}
  : snd
    with signature (@weq (a * b) _) ==> (@weq b _)
      as snd_tuple_weq_morphism.
Proof.
  intros o o' [P Q].
  exact Q.
Qed.

Add Parametric Morphism
    (a b: Type)
   `{WEq a}
   `{WEq b}
  : pair
    with signature (@weq a _) ==> (@weq b _) ==> (@weq (a * b) _)
      as pair_tuple_weq_morphism.
Proof.
  intros o o' Heq p p' Heq'.
  constructor; [ exact Heq
               | exact Heq'
               ].
Qed.

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
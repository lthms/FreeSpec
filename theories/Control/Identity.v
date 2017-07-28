Require Import FreeSpec.Control.
Require Import FreeSpec.WEq.

Local Open Scope free_weq_scope.

Inductive Identity
          (a: Type)
  : Type :=
| identity (x: a)
  : Identity a.

Arguments identity [a] (x).

Definition unwrap
           {a: Type}
           (x: Identity a)
  : a :=
  match x with
  | identity x => x
  end.

Notation "! a" :=
  (unwrap a)
    (at level 41, right associativity).

Definition identity_weq
           {a: Type}
          `{WEq a}
           (x y: Identity a)
  : Prop :=
  !x == !y.

Lemma identity_weq_refl
      {a: Type}
     `{WEq a}
      (x: Identity a)
  : identity_weq x x.
Proof.
  unfold identity_weq.
  reflexivity.
Qed.

Lemma identity_weq_sym
      {a: Type}
     `{WEq a}
      (x y: Identity a)
  : identity_weq x y
    -> identity_weq y x.
Proof.
  unfold identity_weq.
  intro H'.
  symmetry.
  exact H'.
Qed.

Lemma identity_weq_trans
      {a: Type}
     `{WEq a}
      (x y z: Identity a)
  : identity_weq x y
    -> identity_weq y z
    -> identity_weq x z.
Proof.
  unfold identity_weq.
  intros X Y.
  rewrite X.
  exact Y.
Qed.

Add Parametric Relation
    (a: Type)
   `{WEq a}
  : (Identity a) (identity_weq)
    reflexivity  proved by identity_weq_refl
    symmetry     proved by identity_weq_sym
    transitivity proved by identity_weq_trans
      as identity_weq_equiv.

Instance identity_WEq
         (a: Type)
        `{WEq a}
  : WEq (Identity a) :=
  { weq := identity_weq
  }.

Lemma wrap_unwrap_identity
      {a: Type}
     `{WEq a}
      (x: Identity a)
  : identity (! x) == x.
Proof.
  destruct x.
  reflexivity.
Qed.

Lemma wrap_identity_weq
      {a: Type}
     `{WEq a}
     (x y: a)
  : x == y <-> identity x == identity y.
Proof.
  split.
  + intro Heq.
    cbn; unfold identity_weq.
    exact Heq.
  + intro Heq.
    cbn in *.
    unfold identity_weq in Heq.
    exact Heq.
Qed.

Lemma unwrap_identity_weq
      {a: Type}
     `{WEq a}
     (x y: Identity a)
  : !x == !y <-> x == y.
Proof.
  destruct x; destruct y.
  cbn.
  exact (wrap_identity_weq x x0).
Qed.

(** * Functor

 *)

Definition identity_map
           (a b: Type)
           (f:   a -> b)
           (x:   Identity a)
  : Identity b :=
  identity (f (!x)).

Instance identity_Functor
  : Functor Identity :=
  { map := identity_map
  }.
Proof.
  + intros a H x.
    unfold identity_map; unfold id.
    apply wrap_unwrap_identity.
  + intros a b c H u v x.
    apply wrap_identity_weq.
    reflexivity.
Defined.

Definition identity_apply
           (a b: Type)
           (f:   Identity (a -> b))
           (x:   Identity a)
  : Identity b :=
  identity ((!f) (!x)).

Definition identity_pure
           (a: Type)
           (x: a)
  : Identity a :=
  identity x.

Instance identity_Applicative
  : Applicative Identity :=
  { pure := identity_pure
  ; apply := identity_apply
  }.
Proof.
  + intros; apply <- wrap_identity_weq; reflexivity.
  + intros; apply <- wrap_identity_weq; reflexivity.
  + intros; apply <- wrap_identity_weq; reflexivity.
  + intros; apply <- wrap_identity_weq; reflexivity.
Defined.

Definition identity_bind
           (a b: Type)
           (x:   Identity a)
           (f:   a -> Identity b)
  : Identity b :=
  f (!x).

Instance identity_Monad
  : Monad Identity :=
  { bind := identity_bind
  }.
Proof.
  + intros; apply wrap_identity_weq; reflexivity.
  + intros; apply <- wrap_identity_weq; reflexivity.
  + intros a b c C f g h.
    unfold identity_bind.
    reflexivity.
  + intros a b H x f f' Heq.
    cbn.
    unfold identity_weq, identity_bind.
    destruct x.
    cbn in *.
    unfold function_weq in Heq.
    apply unwrap_identity_weq.
    apply Heq.
Defined.
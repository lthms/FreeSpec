Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Classes.
Require Import FreeSpec.Control.Identity.
Require Import FreeSpec.WEq.

Local Open Scope free_weq_scope.

(** * Definition

 *)

Definition ReaderT
           (r: Type)
           (m: Type -> Type)
          `{Monad m}
           (a: Type)
  : Type :=
  r -> m a.

(** * Functor

 *)

Definition reader_map
           {m: Type -> Type}
          `{Monad m}
           {r: Type}
           (a b: Type)
           (f: a -> b)
           (mr: ReaderT r m a)
  : ReaderT r m b :=
  fun x
  => f <$> (mr x).

Instance reader_Functor
         (m: Type -> Type)
        `{Monad m}
         (r: Type)
  : Functor (ReaderT r m) :=
  { map := reader_map
  }.
Proof.
  + intros a A x.
    cbn.
    intros y.
    unfold reader_map.
    exact (functor_identity (x y)).
  + intros a b c C u v x.
    cbn.
    intros y.
    unfold reader_map.
    exact (functor_composition_identity u v (x y)).
Defined.

(** * Applicative

 *)

Definition reader_pure
           {m: Type -> Type}
          `{Monad m}
           {r: Type}
           (a: Type)
           (x: a)
  : ReaderT r m a :=
  fun _
  => pure x.

Definition reader_apply
           {m: Type -> Type}
          `{Monad m}
           {r: Type}
           (a b: Type)
           (f: ReaderT r m (a -> b))
           (x: ReaderT r m a)
  : ReaderT r m b :=
  fun r
  => (f r) <*> (x r).

Instance reader_Applicative
         (m: Type -> Type)
        `{Monad m}
         (r: Type)
  : Applicative (ReaderT r m) :=
  { pure := reader_pure
  ; apply := reader_apply
  }.
Proof.
  + intros a A x.
    cbn.
    intros y.
    unfold reader_apply.
    exact (applicative_identity (x y)).
  + intros a b c C u v w.
    cbn.
    intros y.
    unfold reader_apply, reader_pure.
    exact (applicative_composition (u y) (v y) (w y)).
  + intros a b B v x.
    cbn.
    intros y.
    unfold reader_apply, reader_pure.
    exact (applicative_homomorphism v x).
  + intros a b B u y.
    cbn.
    intros z.
    unfold reader_apply, reader_pure.
    exact (applicative_interchange (u z) y).
Defined.

(** * Monad

 *)

Definition reader_bind
           {m: Type -> Type}
          `{Monad m}
           {r: Type}
           (a b: Type)
           (p: ReaderT r m a)
           (f: a -> ReaderT r m b)
  : ReaderT r m b :=
  fun x
  => p x >>= fun y => f y x.

Instance reader_Monad
         (m: Type -> Type)
        `{Monad m}
         (r: Type)
  : Monad (ReaderT r m) :=
  { bind := reader_bind
  }.
Proof.
  + intros a b B x f.
    cbn.
    intros y.
    unfold reader_bind, reader_pure.
    exact (monad_left_identity x _).
  + intros a A x.
    cbn.
    unfold reader_bind, reader_pure.
    intros y.
    exact (monad_right_identity (x y)).
  + intros a b c C f g h.
    cbn.
    unfold reader_bind, reader_pure.
    intros x.
    exact (monad_bind_associativity (f x) _ _).
  + intros a b B x f f' Heq.
    cbn.
    unfold reader_bind, reader_pure.
    intros y.
    apply monad_bind_morphism.
    intros z.
    apply Heq.
Defined.

(** * Reader Monad

 *)

Instance reader_MonadReader
         (m: Type -> Type)
        `{Monad m}
         (r: Type)
  : MonadReader (ReaderT r m) r :=
  { ask := fun x
           => pure x
  }.

(** * Pure Reader

 *)

Definition Reader r x := ReaderT r Identity x.
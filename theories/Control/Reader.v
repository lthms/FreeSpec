(* FreeSpec
 * Copyright (C) 2018 ANSSI
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>.
 *)

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
  + intros a b B g x.
    cbn.
    intros y.
    unfold reader_map, reader_apply, reader_pure.
    exact (applicative_pure_map g (x y)).
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
  + intros a b B x f.
    cbn.
    intros y.
    unfold reader_map, reader_bind, reader_pure.
    apply monad_bind_map.
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
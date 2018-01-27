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
Require Import FreeSpec.WEq.

Local Open Scope free_control_scope.

(** * Monad Transformer

 *)

Class MonadTrans
      (t: forall (m: Type -> Type) `{Monad m}, Type -> Type)
  := { monad_trans_is_monad (m: Type -> Type) `{Monad m} :> Monad (t m)
     ; lift (m: Type -> Type) `{Monad m} (a: Type): m a -> t m a
     }.

Arguments lift [t _ m _ a] (_).

(** * State Monad

 *)

Class MonadState
      (m: Type -> Type)
      (s: Type) :=
  { monadstate_is_monad :> Monad m
  ; put: s -> m unit
  ; get: m s
  }.

Arguments put [m s _] (_).
Arguments get [m s _].

Definition modify
           {s: Type}
           {m: Type -> Type}
          `{MonadState m s}
           (f: s -> s)
  : m unit :=
  x <- get                             ;
  put (f x).

Definition gets
           {s a: Type}
           {m:   Type -> Type}
          `{MonadState m s}
           (f: s -> a)
  : m a :=
  x <- get            ;
  pure (f x).

Instance monadtransform_state
         (t: forall (m: Type -> Type) `{Monad m}, Type -> Type)
        `{MonadTrans t}
         (s: Type)
         (m: Type -> Type)
        `{MonadState m s}
  : MonadState (t m) s :=
  { put := fun x => lift (put x)
  ; get := lift get
  }.

(** * Reader Monad

 *)

Class MonadReader
      (m: Type -> Type)
      (r: Type) :=
  { monadreader_is_monad :> Monad m
  ; ask: m r
  }.

Arguments ask [m r _].

Instance monadtransform_reader
         (t: forall (m: Type -> Type) `{Monad m}, Type -> Type)
        `{MonadTrans t}
         (r: Type)
         (m: Type -> Type)
        `{MonadReader m r}
  : MonadReader (t m) r :=
  { ask := lift ask
  }.
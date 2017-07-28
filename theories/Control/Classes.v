Require Import FreeSpec.Control.
Require Import FreeSpec.WEq.

(** Monad Transformer

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
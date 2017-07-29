Require Import FreeSpec.Control.
Require Import FreeSpec.WEq.

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
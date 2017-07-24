Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.

Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Identity.
Require Import FreeSpec.WEq.

Local Close Scope nat_scope.
Local Open Scope free_control_scope.

Definition StateT
           (s: Type)
           (m: Type -> Type)
          `{Monad m}
           (a: Type)
  := s -> m (a * s).

Definition State
           (s: Type) :=
  StateT s Identity.

Definition state_map
           {m: Type -> Type}
          `{Monad m}
           {s:   Type}
           (a b: Type)
           (f:   a -> b)
           (fs:  StateT s m a)
  : StateT s m b :=
  fun s
  => o <- fs s                                                      ;
     pure (f (fst o), (snd o)).

Instance state_Functor
         (m: Type -> Type)
        `{Monad m}
         (s: Type)
  : Functor (StateT s m) :=
  { map := state_map
  }.

Definition state_apply
           {m: Type -> Type}
          `{Monad m}
           {s:   Type}
           (a b: Type)
           (f:   StateT s m (a -> b))
           (fs:  StateT s m a)
  : StateT s m b :=
  fun s
  => u <- f s                                                       ;
     v <- fs (snd u)                                                ;
     pure ((fst u) (fst v), snd v).

Instance state_Apply
         (m: Type -> Type)
        `{Monad m}
         (s: Type)
  : Apply (StateT s m) :=
  { apply := state_apply
  }.

Definition state_bind
           {m: Type -> Type}
          `{Monad m}
           {s:   Type}
           (a b: Type)
           (fs:  StateT s m a)
           (f:   a -> StateT s m b)
  : StateT s m b :=
  fun x
  => u <- fs x                                                       ;
     pure (f (fst u)) (snd u).

Instance state_Bind
         (m: Type -> Type)
        `{Monad m}
         (s: Type)
  : Bind (StateT s m) :=
  { bind := state_bind
  }.

Definition state_pure
           {m: Type -> Type}
          `{Monad m}
           {s: Type}
           (a: Type)
           (x: a)
  : StateT s m a :=
  fun t => pure (x, t).

Instance state_Applicative
         (m: Type -> Type)
        `{Monad m}
         (s: Type)
  : Applicative (StateT s m) :=
  { pure := state_pure
  }.

Instance state_Monad
         (m: Type -> Type)
        `{Monad m}
         (s: Type)
  : Monad (StateT s m) :=
  {
  }.

Definition state_lift
           {s: Type}
           (m: Type -> Type)
          `{Monad m}
           (a: Type)
           (x: m a)
  : StateT s m a :=
  fun s
  => o <- x                                                          ;
     pure (o, s).

Instance state_MonadTrans
         (s: Type)
  : MonadTrans (StateT s) :=
  { lift := state_lift
  }.

Definition runState
           {m: Type -> Type}
          `{Monad m}
           {s a: Type}
           (ps:  StateT s m a)
           (x:   s)
  : m (a * s) :=
  ps x.

Definition evalState
           {m: Type -> Type}
          `{Monad m}
           {s a: Type}
           (ps:  StateT s m a)
           (x:   s)
  : m a :=
  fst <$> runState ps x.

Definition execState
           {s a: Type}
           (ps:  State s a)
           (x:   s)
  : s :=
  snd <$> runState ps x.
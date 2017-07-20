Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.

Require Import FreeSpec.Control.
Require Import FreeSpec.WEq.

Definition State
           (s: Type)
           (a: Type)
  := s -> a * s.

Definition state_map
           {s:   Type}
           {a b: Type}
           (f:   a -> b)
           (fs:  State s a)
  : State s b :=
  fun s => let (x, s') := fs s
           in (f x, s').

Instance state_Functor
         (s: Type)
  : Functor (State s) :=
  { map := @state_map s
  }.

Definition state_apply
           {s:   Type}
           {a b: Type}
           (f:   State s (a -> b))
           (fs:  State s a)
  : State s b :=
  fun s
  => let (g, s') := f s in
     let (x', s'') := fs s'
     in (g x', s'').

Instance state_Apply
         (s: Type)
  : Apply (State s) :=
  { apply := @state_apply s
  }.

Definition state_bind
           {s:   Type}
           {a b: Type}
           (fs:  State s a)
           (f:   a -> State s b)
  : State s b :=
  fun x
  => let (y, x') := fs x
     in f y x'.

Instance state_Bind
         (s: Type)
  : Bind (State s) :=
  { bind := @state_bind s
  }.

Definition state_pure
           {s: Type}
           {a: Type}
           (x: a)
  : State s a :=
  fun t => (x, t).

Instance state_Applicative
         (s: Type)
  : Applicative (State s) :=
  { pure := @state_pure s
  }.

Instance state_Monad
         (s: Type)
  : Monad (State s) :=
  {
  }.

Definition runState
           {s a: Type}
           (ps:  State s a)
           (x:   s)
  : a * s :=
  ps x.

Definition evalState
           {s a: Type}
           (ps:  State s a)
           (x:   s)
  : a :=
  fst (runState ps x).

Definition execState
           {s a: Type}
           (ps:  State s a)
           (x:   s)
  : s :=
  snd (runState ps x).
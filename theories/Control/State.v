Set Universe Polymorphism.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.

Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Identity.
Require Import FreeSpec.WEq.

Local Close Scope nat_scope.
Local Open Scope free_control_scope.
Local Open Scope free_weq_scope.

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

Lemma state_functor_identity
      (m: Type -> Type)
     `{Monad m}
      {s: Type}
      {a: Type}
      (ps: StateT s m a)
  : state_map _ _ id ps == id ps.
Proof.
Admitted.

Lemma state_functor_composition_identity
      (m: Type -> Type)
     `{Monad m}
      {s: Type}
      {a b c: Type}
      (u: a -> b)
      (v: b -> c)
      (ps: StateT s m a)
  : state_map _ _ (u <<< v) ps == ((state_map _ _ u) <<< (state_map _ _ v)) ps.
Proof.
Admitted.

Instance state_Functor
         (m: Type -> Type)
        `{Monad m}
         (s: Type)
  : Functor (StateT s m) :=
  { map := state_map
  }.
Proof.
  + apply state_functor_identity.
  + apply state_functor_composition_identity.
Defined.

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

Lemma state_apply_composition
      (m: Type -> Type)
     `{Monad m}
      {s: Type}
      (a b c : Type)
      (u: StateT s m (b -> c))
      (v: StateT s m (a -> b))
      (w : StateT s m a):
  state_apply _ _ (state_apply _ _ (compose <$> u) v) w
  == state_apply _ _ u (state_apply _ _ v w).
Proof.
Admitted.

Instance state_Apply
         (m: Type -> Type)
        `{Monad m}
         (s: Type)
  : Apply (StateT s m) :=
  { apply := state_apply
  }.
Proof.
  + apply state_apply_composition.
Defined.

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

Lemma state_bind_associativity
      (m: Type -> Type)
     `{Monad m}
      {s: Type}
      (a b c : Type)
      (f : StateT s m a)
      (g : a -> StateT s m b)
      (h : b -> StateT s m c)
  : state_bind b c (state_bind a b f g) h
    == state_bind a c f (fun x : a => state_bind b c (g x) h).
Proof.
Admitted.

Instance state_Bind
         (m: Type -> Type)
        `{Monad m}
         (s: Type)
  : Bind (StateT s m) :=
  { bind := state_bind
  }.
Proof.
  + apply state_bind_associativity.
Defined.

Definition state_pure
           {m: Type -> Type}
          `{Monad m}
           {s: Type}
           (a: Type)
           (x: a)
  : StateT s m a :=
  fun t => pure (x, t).

Lemma state_applicative_identity
      (m: Type -> Type)
     `{Monad m}
      {s: Type}
      {a : Type}
      (v : StateT s m a):
  state_pure (a -> a) id <*> v == v.
Proof.
Admitted.

Lemma state_applicative_composition
      (m: Type -> Type)
     `{Monad m}
      {s: Type}
      {a b c : Type}
      (u : StateT s m (b -> c))
      (v : StateT s m (a -> b))
      (w : StateT s m a)
  : state_pure ((b -> c) -> (a -> b) -> a -> c) compose <*> u <*> v <*> w
    == u <*> (v <*> w).
Proof.
Admitted.

Lemma state_applicative_homomorphism
      (m: Type -> Type)
     `{Monad m}
      {s: Type}
      {a b: Type}
      (v : a -> b)
      (x : a)
  : state_pure (s:=s) (a -> b) v <*> state_pure a x == state_pure b (v x).
Proof.
Admitted.

Lemma state_applicative_interchange
      (m: Type -> Type)
     `{Monad m}
      {s: Type}
      (a b : Type)
      (u : StateT s m (a -> b))
      (y : a)
  : u <*> state_pure a y
    == state_pure ((a -> b) -> b) (fun z : a -> b => z y) <*> u.
Proof.
Admitted.

Instance state_Applicative
         (m: Type -> Type)
        `{Monad m}
         (s: Type)
  : Applicative (StateT s m) :=
  { pure := state_pure
  }.
Proof.
  + apply state_applicative_identity.
  + apply state_applicative_composition.
  + apply state_applicative_homomorphism.
  + apply state_applicative_interchange.
Defined.

Lemma state_monad_left_identity
      (m: Type -> Type)
     `{Monad m}
      {s: Type}
      (a b : Type)
      (x : a)
      (f : a -> StateT s m b)
  : (a <- pure x; f a) == f x.
Proof.
Admitted.

Lemma state_monad_right_identity
      (m: Type -> Type)
     `{Monad m}
      {s: Type}
      (a : Type)
      (x : StateT s m a)
  : (y <- x; pure y) == x.
Proof.
Admitted.

Instance state_Monad
         (m: Type -> Type)
        `{Monad m}
         (s: Type)
  : Monad (StateT s m) :=
  {
  }.
Proof.
  + apply state_monad_left_identity.
  + apply state_monad_right_identity.
Defined.

Definition state_lift
           (s: Type)
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
  { lift := state_lift s
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
           {m: Type -> Type}
          `{Monad m}
           {s a: Type}
           (ps:  StateT s m a)
           (x:   s)
  : m s :=
  snd <$> runState ps x.

Definition get
           {m: Type -> Type}
          `{Monad m}
           {s: Type}
  : StateT s m s :=
  fun x
  => pure (x, x).

Definition put
           {m: Type -> Type}
          `{Monad m}
           {s: Type}
           (x: s)
  : StateT s m unit :=
  fun _
  => pure (tt, x).
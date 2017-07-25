Set Universe Polymorphism.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.

Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Identity.
Require Import FreeSpec.WEq.

Local Close Scope nat_scope.
Local Open Scope free_control_scope.
Local Open Scope free_weq_scope.

(** * Definition

 *)

Definition StateT
           (s: Type)
           (m: Type -> Type)
           `{Monad m}
           (a: Type)
  : Type :=
  s -> m (a * s).

Definition runStateT
           {m: Type -> Type}
          `{Monad m}
           {s a: Type}
           (ps:  StateT s m a)
           (x:   s)
  : m (a * s) :=
  ps x.

Definition evalStateT
           {m: Type -> Type}
          `{Monad m}
           {s a: Type}
           (ps:  StateT s m a)
           (x:   s)
  : m a :=
  fst <$> runStateT ps x.

Definition execStateT
           {m: Type -> Type}
          `{Monad m}
           {s a: Type}
           (ps:  StateT s m a)
           (x:   s)
  : m s :=
  snd <$> runStateT ps x.

(** * Monadic Interface

 *)

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

(** * State Monad

 *)

Definition state_map
           {m: Type -> Type}
          `{Monad m}
           {s:   Type}
           (a b: Type)
           (f:   a -> b)
           (fs:  StateT s m a)
  : StateT s m b :=
    fun s
    => o <- fs s                                                     ;
       pure (f (fst o), (snd o)).

Definition statet_weq
           {m: Type -> Type}
          `{Monad m}
           {s:   Type}
          `{WEq s}
           {a: Type}
          `{WEq a}
           (p g: StateT s m a)
  : Prop :=
  forall (x: s),
    fst <$> p x == fst <$> g x
    /\ snd <$> p x == snd <$> g x.

Lemma statet_weq_refl
      {m: Type -> Type}
     `{Monad m}
      {s:   Type}
     `{WEq s}
      {a: Type}
     `{WEq a}
      (p: StateT s m a)
  : statet_weq p p.
Proof.
  split.
  + reflexivity.
  + reflexivity.
Qed.

Lemma statet_weq_sym
      {m: Type -> Type}
     `{Monad m}
      {s:   Type}
     `{WEq s}
      {a: Type}
     `{WEq a}
      (p q: StateT s m a)
  : statet_weq p q
    -> statet_weq q p.
Proof.
  intros G x.
  assert (G': fst <$> p x == fst <$> q x /\ snd <$> p x == snd <$> q x)
    by exact (G x).
  destruct G' as [G1 G2].
  split; symmetry; [ exact G1
                   | exact G2
                   ].
Qed.

Lemma statet_weq_trans
      {m: Type -> Type}
     `{Monad m}
      {s:   Type}
     `{WEq s}
      {a: Type}
     `{WEq a}
      (p q r: StateT s m a)
  : statet_weq p q
    -> statet_weq q r
    -> statet_weq p r.
Proof.
  intros Q R x.
  assert (Q': fst <$> p x == fst <$> q x /\ snd <$> p x == snd <$> q x)
    by exact (Q x).
  assert (R': fst <$> q x == fst <$> r x /\ snd <$> q x == snd <$> r x)
    by exact (R x).
  destruct Q' as [Q1 Q2].
  destruct R' as [R1 R2].
  split.
  + rewrite Q1; exact R1.
  + rewrite Q2; exact R2.
Qed.

Add Parametric Relation
    (m: Type -> Type)
   `{Monad m}
    (s:   Type)
   `{WEq s}
    (a: Type)
   `{WEq a}
  : (StateT s m a) (statet_weq)
    reflexivity proved by statet_weq_refl
    symmetry proved by statet_weq_sym
    transitivity proved by statet_weq_trans
      as statet_weq_equiv.

Instance statet_WEq
         (m: Type -> Type)
        `{Monad m}
         (s:   Type)
        `{WEq s}
         (a: Type)
        `{WEq a}
  : WEq (StateT s m a) :=
  { weq := statet_weq
  }.

Lemma state_functor_identity
      (m: Type -> Type)
     `{Monad m}
      {s: Type}
     `{WEq s}
      {a: Type}
     `{WEq a}
      (ps: StateT s m a)
  : state_map _ _ id ps == id ps.
Proof.
  constructor.
  + unfold state_map.
    unfold id.
Admitted.

Lemma state_functor_composition_identity
      (m: Type -> Type)
     `{Monad m}
      {s: Type}
     `{WEq s}
      {a b c: Type}
     `{WEq c}
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
        `{WEq s}
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
     `{WEq s}
      (a b c : Type)
     `{WEq c}
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
        `{WEq s}
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
     f (fst u) (snd u).

Lemma state_bind_associativity
      (m: Type -> Type)
     `{Monad m}
      {s: Type}
     `{WEq s}
      (a b c : Type)
     `{WEq c}
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
        `{WEq s}
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
      {m: Type -> Type}
     `{Monad m}
      {s: Type}
     `{WEq s}
      {a : Type}
     `{WEq a}
      (v : StateT s m a):
  state_pure (a -> a) id <*> v == v.
Proof.
Admitted.

Lemma state_applicative_composition
      {m: Type -> Type}
     `{Monad m}
      {s: Type}
     `{WEq s}
      {a b c : Type}
     `{WEq c}
      (u : StateT s m (b -> c))
      (v : StateT s m (a -> b))
      (w : StateT s m a)
  : state_pure ((b -> c) -> (a -> b) -> a -> c) compose <*> u <*> v <*> w
    == u <*> (v <*> w).
Proof.
Admitted.

Lemma state_applicative_homomorphism
      {m: Type -> Type}
     `{Monad m}
      {s: Type}
     `{WEq s}
      {a b: Type}
     `{WEq b}
      (v: a -> b)
      (x: a)
  : state_pure _ v <*> state_pure _ x == (state_pure _ (v x): StateT s m b).
Proof.
Admitted.

Lemma state_applicative_interchange
      (m: Type -> Type)
     `{Monad m}
      {s: Type}
     `{WEq s}
      (a b : Type)
     `{WEq b}
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
        `{WEq s}
  : Applicative (StateT s m) :=
  { pure := state_pure
  }.
Proof.
  + apply (@state_applicative_identity m H s H0).
  + apply (@state_applicative_composition m H s H0).
  + apply (@state_applicative_homomorphism m H s H0).
  + apply (@state_applicative_interchange m H s H0).
Defined.

Lemma state_monad_left_identity
      (m: Type -> Type)
     `{Monad m}
      {s: Type}
     `{WEq s}
      (a b : Type)
     `{WEq b}
      (x : a)
      (f : a -> StateT s m b)
  : (a <- pure x; f a) == f x.
Proof.
Admitted.

Lemma state_monad_right_identity
      (m: Type -> Type)
     `{Monad m}
      {s: Type}
     `{WEq s}
      (a : Type)
     `{WEq a}
      (x : StateT s m a)
  : (y <- x; pure y) == x.
Proof.
Admitted.

Instance state_Monad
         (m: Type -> Type)
        `{Monad m}
         (s: Type)
        `{WEq s}
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
        `{WEq s}
  : MonadTrans (StateT s) :=
  { lift := state_lift s
  }.

(** * Pure Monad State

 *)

Definition State
           (s: Type) :=
  StateT s Identity.
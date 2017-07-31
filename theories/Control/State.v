Set Universe Polymorphism.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.

Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Classes.
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
    => (fun o => (f (fst o), snd o)) <$> fs s.

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
  cbn.
  unfold function_weq, state_map.
  intros x.
  assert (R1: (fun (o: a * s) => (id (fst o), snd o)) = id). {
    apply functional_extensionality.
    intro o; destruct o; reflexivity.
  }
  rewrite R1.
  apply functor_identity.
Qed.

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
  cbn.
  unfold function_weq, state_map.
  intros x.
  assert (R1: (fun o : a * s => ((v >>> u) (fst o), snd o))
              = ((fun o : b * s => (v (fst o), snd o))
                   >>> (fun o : a * s => (u (fst o), snd o)))). {
    apply functional_extensionality.
    intros y.
    destruct y.
    cbn.
    assert (R2: ((fun o : b * s => (v (fst o), snd o)) >>> (fun o : a * s => (u (fst o), snd o)))
                = (fun o => ((v >>> u) (fst o), snd o))). {
      apply functional_extensionality.
      intros z.
      destruct z.
      reflexivity.
    }
    rewrite R2.
    reflexivity.
  }
  rewrite R1.
  apply functor_composition_identity.
Qed.

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
  fun x
  => u <- f x                                                       ;
     v <- fs (snd u)                                                ;
     pure ((fst u) (fst v), snd v).

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
  state_apply _ _ (state_pure (a -> a) id) v == v.
Proof.
  cbn.
  unfold function_weq, state_apply.
  intros x.
  assert (R1: (u <- state_pure (a -> a) id x; v0 <- v (snd u); pure (fst u (fst v0), snd v0))
              == (v0 <- v x; pure (id (fst v0), snd v0))). {
    cbn.
    unfold function_weq, state_apply, state_pure, id.
    rewrite monad_left_identity.
    reflexivity.
  }
  rewrite R1.
  unfold id.
  assert (R2: (fun (v0: a * s) => pure (f:=m) (fst v0, snd v0))
              = (fun v0 => pure v0)). {
    apply functional_extensionality.
    intro y.
    destruct y.
    reflexivity.
  }
  rewrite R2.
  rewrite monad_right_identity.
  reflexivity.
Qed.

Lemma state_applicative_homomorphism
      {m: Type -> Type}
     `{Monad m}
      {s: Type}
     `{WEq s}
      {a b: Type}
     `{WEq b}
      (v: a -> b)
      (x: a)
  : state_apply _ _ (state_pure _ v) (state_pure _ x) == (state_pure _ (v x): StateT s m b).
Proof.
  cbn.
  unfold function_weq, state_apply, state_pure.
  intro y.
  rewrite monad_left_identity.
  cbn.
  rewrite monad_left_identity.
  cbn.
  reflexivity.
Qed.

Lemma state_applicative_interchange
      (m: Type -> Type)
     `{Monad m}
      {s: Type}
     `{WEq s}
      (a b : Type)
     `{WEq b}
      (u : StateT s m (a -> b))
      (y : a)
  : state_apply _ _ u (state_pure a y)
    == state_apply _ _ (state_pure ((a -> b) -> b) (fun z : a -> b => z y)) u.
Proof.
  cbn.
  unfold function_weq.
  intro x.
  unfold state_apply, state_pure.
  rewrite monad_left_identity.
  cbn.
  assert (R1: (fun (u0: ((a -> b) * s))
               => (v <- pure (f:=m) (y, snd u0);
                   pure (fst u0 (fst v), snd v)))
             == (fun (v: ((a -> b) * s))
                  => pure (f:=m) (fst v y, snd v))). {
    cbn.
    unfold function_weq.
    intros z.
    rewrite monad_left_identity.
    reflexivity.
  }
  rewrite R1.
  reflexivity.
Qed.

Instance state_Applicative
         (m: Type -> Type)
        `{Monad m}
         (s: Type)
        `{WEq s}
  : Applicative (StateT s m) :=
  { pure := state_pure
  ; apply := state_apply
  }.
Proof.
  + apply (@state_applicative_identity m H s H0).
  + intros a b c C u v w.
    cbn.
    unfold function_weq, state_apply, state_pure.
    intro x.
    assert (R1: (u0 <- pure (@compose a b c, x); v0 <- u (snd u0); pure (fst u0 (fst v0), snd v0))
                == (v0 <- u (snd (@compose a b c, x)); pure (fst (compose, x) (fst v0), snd v0))). {
      rewrite monad_left_identity.
      reflexivity.
    }
    repeat rewrite monad_bind_associativity.
    rewrite monad_left_identity.
    repeat rewrite monad_bind_associativity.
    cbn.
    assert (R2: (fun x0
                 => (x1 <- pure (compose (fst x0), snd x0);
                     u0 <- (v0 <- v (snd x1); pure (fst x1 (fst v0), snd v0));
                     v0 <- w (snd u0); pure (fst u0 (fst v0), snd v0)))
                == (fun u0
                    => v0 <- (u1 <- v (snd u0); v0 <- w (snd u1); pure (fst u1 (fst v0), snd v0));
                       pure (fst u0 (fst v0), snd v0))). {
      intros y.
      repeat rewrite monad_left_identity.
      repeat rewrite monad_bind_associativity.
      cbn.
      assert (R3: (fun x0
                  => (u0 <- pure (fst y >>> fst x0, snd x0);
                      v0 <- w (snd u0); pure (fst u0 (fst v0), snd v0)))
                  == fun x0
                     => (v0 <- (v0 <- w (snd x0); pure (fst x0 (fst v0), snd v0));
                         pure (fst y (fst v0), snd v0))). {
        cbn.
        intros z.
        repeat rewrite monad_left_identity.
        repeat rewrite monad_bind_associativity.
        cbn.
        assert (R4: (fun (v0: a * s)
                     => pure (f:=m) ((fst y >>> fst z) (fst v0), snd v0))
                    == (fun x0
                        => v0 <- pure (fst z (fst x0), snd x0); pure (fst y (fst v0), snd v0))). {
          cbn.
          intros q.
          repeat rewrite monad_left_identity.
          cbn.
          unfold compose.
          reflexivity.
        }
        apply monad_bind_morphism.
        intros n.
        rewrite monad_left_identity.
        reflexivity.
      }
      rewrite (monad_bind_morphism _ _ _ R3).
      reflexivity.
    }
    rewrite (monad_bind_morphism _ _ _ R2).
    reflexivity.
  + apply (@state_applicative_homomorphism m H s H0).
  + apply (@state_applicative_interchange m H s H0).
  + intros a b B g x.
    cbn.
    intros y.
    unfold state_apply, state_pure.
    rewrite monad_left_identity.
    cbn.
    unfold state_map.
    remember (fun o : a * s => (g (fst o), snd o)) as f.
    assert ((x y >>= (fun (v: a * s)
                      => pure (f:=m) (g (fst v), snd v)))
           == (x y >>= (fun v => pure (f v)))).
    rewrite Heqf.
    reflexivity.
    rewrite H1.
    apply monad_bind_map.
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
  cbn.
  unfold state_bind, function_weq.
  intros x.
  rewrite monad_bind_associativity.
  reflexivity.
Qed.

Instance state_Monad
         (m: Type -> Type)
        `{Monad m}
         (s: Type)
        `{WEq s}
  : Monad (StateT s m) :=
  { bind := state_bind
  }.
Proof.
  + intros a b B x f.
    cbn.
    unfold function_weq, state_bind, state_pure.
    intros y.
    rewrite monad_left_identity.
    reflexivity.
  + intros a A x.
    cbn.
    unfold function_weq, state_bind, state_pure.
    intros y.
    assert (R1: (fun (u: (a * s)) => pure (f:=m) (fst u, snd u))
                = fun (u: (a * s)) => pure u). {
      apply functional_extensionality.
      intros [z  z'].
      reflexivity.
    }
    rewrite R1.
    apply monad_right_identity.
  + apply state_bind_associativity.
  + intros a b B p f f' Heq.
    cbn.
    unfold function_weq, state_bind.
    intros x.
    assert (R1: (fun u => f (fst u) (snd u))
                == fun u => f' (fst u) (snd u)). {
      cbn.
      intros y.
    apply Heq.
    }
    rewrite (monad_bind_morphism _ _ _ R1).
    reflexivity.
  + intros a b B x f.
    unfold state_bind.
    intros y.
    apply monad_bind_map.
Defined.

(** * Transformer Instance

 *)

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

(** * State Instance

 *)

Definition state_get
           (m: Type -> Type)
          `{Monad m}
           (s: Type)
  : StateT s m s :=
  fun x
  => pure (x, x).

Definition state_put
           (m: Type -> Type)
          `{Monad m}
           (s: Type)
           (x: s)
  : StateT s m unit :=
  fun _
  => pure (tt, x).

Instance state_StateMonad
         (m: Type -> Type)
        `{Monad m}
         (s: Type)
        `{WEq s}
  : MonadState (StateT s m) s :=
  { get := state_get m s
  ; put := state_put m s
  }.

(** * Pure Monad State

 *)

Definition State
           (s: Type) :=
  StateT s Identity.
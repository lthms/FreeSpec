Set Universe Polymorphism.

Require Import Coq.Program.Basics.
Require Import Coq.Classes.Equivalence.

Require Import FreeSpec.WEq.

Notation "f <<< g" := (compose g f) (at level 50).
Notation "f >>> g" := (compose f g) (at level 50).

Instance function_WEq
         (a b: Type)
  : WEq (a -> b) :=
  { weq := eq
  }.

(** * Functor

 *)

Local Open Scope free_weq_scope.

Class Functor
      (f: Type -> Type)
  := { functor_has_eq :> forall {a}, WEq (f a)
     ; map {a b: Type}
           (g:   a -> b)
           (x:   f a)
       : f b
     ; functor_identity {a: Type}
                        (x: f a)
       : map (@id a) x == id x
     ; functor_composition_identity {a b c: Type}
                                    (u:     a -> b)
                                    (v:     b -> c)
                                    (x:     f a)
       : map (u <<< v) x == ((map u) <<< (map v)) x
     }.

Arguments map [f _ a b] (_ _).
Arguments functor_identity [f _ a].
Arguments functor_composition_identity [f _ a].

Notation "f <$> g" :=
  (map f g)
    (at level 27, left associativity).

(** * Apply

 *)

Reserved Notation "f <*> g" (at level 28, left associativity).

Class Apply
      (f: Type -> Type)
  := { apply_is_functor :> Functor f
     ; apply: forall {a b: Type},
         f (a -> b)
         -> f a
         -> f b
       where "f <*> g" := (apply f g)
     }.

Arguments apply [f _ a b].

Notation "f <*> g" :=
  (apply f g)
    (at level 28, left associativity).

(** * Applicative

 *)

Class Applicative
      (f: Type -> Type)
  := { applicative_is_apply :> Apply f
     ; pure: forall {a: Type},
         a -> f a
     }.

Arguments pure [f _ a] (x).

(** * Bind

 *)

Reserved Notation "f >>= g" (at level 28, left associativity).

Class Bind
      (m: Type -> Type)
  := { bind_is_apply :> Apply m
     ; bind: forall {a b: Type},
         m a
         -> (a -> m b)
         -> m b
       where "f >>= g" := (bind f g)
     ; bind_associativity: forall {a b c: Type}
                                  (f:     m a)
                                  (g:     a -> m b)
                                  (h:     b -> m c),
         (f >>= g) >>= h == f >>= (fun x => (g x) >>= h)

     }.

Arguments bind [m _ a b] (f g).
Arguments bind_associativity [m _ a b c] (f g h).

Notation "f >>= g" := (bind f g) (at level 28, left associativity).

Definition join
           {m: Type -> Type}
          `{Bind m}
           {a: Type}
           (x: m (m a))
  : m a :=
  x >>= id.

(** * Monad

 *)

Class Monad
      (m: Type -> Type)
  := { monad_is_applicative :> Applicative m
     ; monad_is_bind :> Bind m
     ; monad_left_identity: forall {a b: Type}
                                   (x:   a)
                                   (f:   a -> m b),
         pure x >>= f == f x
     ; monad_right_identity: forall {a: Type}
                                    (x: m a),
         x >>= (fun y => pure y) == x
     }.

Arguments monad_left_identity [m _ a b] (x f).
Arguments monad_right_identity [m _ a] (x).

(** * Monad Transformer

 *)

Class MonadTrans
      (t: forall (m: Type -> Type) `{Monad m}, Type -> Type)
  := { monad_trans_is_monad (m: Type -> Type) `{Monad m} :> Monad (t m)
     ; lift (m: Type -> Type) `{Monad m} (a: Type): m a -> t m a
     }.

Arguments lift [t _ m _ a] (_).

Notation "a <- p ; q" :=
  (bind p (fun a => q)) (at level 99, right associativity, p at next level)
  : free_control_scope.
Notation "p ;; q" :=
  (bind p (fun _ => q)) (at level 99, right associativity)
  : free_control_scope.

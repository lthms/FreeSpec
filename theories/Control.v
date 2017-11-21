Set Universe Polymorphism.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Setoids.Setoid.

Require Import FreeSpec.WEq.

Local Open Scope free_weq_scope.

Polymorphic Definition compose
            {a b c: Type}
            (g: b -> c)
            (f: a -> b)
  : a -> c :=
  fun (x: a)
  => g (f x).

Polymorphic Definition id
            {a: Type}
            (x: a)
  : a :=
  x.

Notation "f <<< g" := (compose f g) (at level 50).
Notation "f >>> g" := (compose g f) (at level 50).
Notation "f $ x" := (f x) (only parsing, at level 99, right associativity).

(** * Functor

 *)

Class Functor
      (f: Type -> Type)
  := { functor_has_eq :> forall {a: Type}
                               `{WEq a},
           WEq (f a)
     ; map {a b: Type}
           (g:   a -> b)
           (x:   f a)
       : f b
     ; functor_identity {a: Type}
                       `{WEq a}
                        (x: f a)
       : map (@id a) x == id x
     ; functor_composition_identity {a b c: Type}
                                   `{WEq c}
                                    (u:     b -> c)
                                    (v:     a -> b)
                                    (x:     f a)
       : map (u <<< v) x == ((map u) <<< (map v)) x
     }.

Arguments map [f _ a b] (_ _).
Arguments functor_identity [f _ a _] (x).
Arguments functor_composition_identity [f _ a b c _] (u v x).

Notation "f <$> g" :=
  (map f g)
    (at level 27, left associativity).

(** * Applicative

 *)

Reserved Notation "f <*> g" (at level 28, left associativity).

Class Applicative
      (f: Type -> Type)
  := { applicative_is_functor :> Functor f
     ; pure: forall {a: Type},
         a -> f a
     ; apply: forall {a b: Type},
         f (a -> b)
         -> f a
         -> f b
       where "f <*> g" := (apply f g)
     ; applicative_identity: forall {a: Type}
                                   `{WEq a}
                                    (v: f a),
         pure id <*> v == v
     ; applicative_composition: forall {a b c: Type}
                                      `{WEq c}
                                       (u:     f (b -> c))
                                       (v:     f (a -> b))
                                       (w:     f a),
         pure compose <*> u <*> v <*> w == u <*> (v <*> w)
     ; applicative_homomorphism: forall {a b: Type}
                                       `{WEq b}
                                        (v:   a -> b)
                                        (x:   a),
         (pure v) <*> (pure x) == pure (v x)
     ; applicative_interchange: forall {a b: Type}
                                      `{WEq b}
                                       (u: f (a -> b))
                                       (y: a),
         u <*> (pure y) == (pure (fun z => z y)) <*> u
     ; applicative_pure_map: forall {a b: Type}
                                   `{WEq b}
                                    (g: a -> b)
                                    (x: f a),
         g <$> x == pure g <*> x
     }.

Notation "f <*> g" :=
  (apply f g)
    (at level 28, left associativity).

Arguments pure [f _ a] (x).
Arguments apply [f _ a b] (_ _).
Arguments applicative_identity [f _ a _] (v).
Arguments applicative_composition [f _ a b c _] (u v w).
Arguments applicative_homomorphism [f _ a b _] (v x).
Arguments applicative_interchange [f _ a b _] (u y).
Arguments applicative_pure_map [f _ a b _] (g x).

(** * Monad

 *)

Reserved Notation "f >>= g" (at level 28, left associativity).

Class Monad
      (m: Type -> Type)
  := { monad_is_apply :> Applicative m
     ; bind: forall {a b: Type},
         m a
         -> (a -> m b)
         -> m b
       where "f >>= g" := (bind f g)
     ; monad_left_identity: forall {a b: Type}
                                  `{WEq b}
                                   (x:   a)
                                   (f:   a -> m b),
         pure x >>= f == f x
     ; monad_right_identity: forall {a: Type}
                                   `{WEq a}
                                    (x: m a),
         x >>= (fun y => pure y) == x
     ; monad_bind_associativity: forall {a b c: Type}
                                       `{WEq c}
                                        (f:     m a)
                                        (g:     a -> m b)
                                        (h:     b -> m c),
         (f >>= g) >>= h == f >>= (fun x => (g x) >>= h)
     ; monad_bind_morphism {a b: Type}
                          `{WEq b}
                           (x: m a)
                           (f f': a -> m b)
       : f == f' -> bind x f == bind x f'
     ; monad_bind_map {a b: Type}
                     `{WEq b}
                      (x: m a)
                      (f: a -> b)
       : f <$> x == (x >>= (fun y => pure (f y)))
     }.

Arguments bind [m _ a b] (f g).
Arguments monad_left_identity [m _ a b _] (x f).
Arguments monad_right_identity [m _ a _] (x).
Arguments monad_bind_associativity [m _ a b c _] (f g h).
Arguments monad_bind_morphism [m _ a b _] (x f f').
Arguments monad_bind_map [m _ a b _] (x f).

Add Parametric Morphism
    (m: Type -> Type)
   `{M: Monad m}
    (a b: Type)
   `{WEq a}
   `{B: WEq b}
  : (@bind m M a b)
    with signature (@eq (m a))
                   ==> (@weq (a -> m b) _)
                   ==> (@weq (m b) functor_has_eq)
      as bind_morphism_decl.
Proof.
  intros x f f' Heq.
  apply (monad_bind_morphism x f f' Heq).
Qed.

Notation "f >>= g" := (bind f g) (at level 28, left associativity).

Definition join
           {m: Type -> Type}
          `{Monad m}
           {a: Type}
           (x: m (m a))
  : m a :=
  x >>= id.

Definition void
           {m:  Type -> Type} `{Monad m}
           {a:  Type}
           (x:  m a)
  : m unit :=
  x >>= fun _ => pure tt.

Definition when
           {m:     Type -> Type} `{Monad m}
           {a:     Type}
           (cond:  bool)
           (x:     m a)
  : m unit :=
  if cond
  then void x
  else pure tt.

Notation "a <- p ; q" :=
  (bind p (fun a => q)) (at level 100, right associativity, p at next level)
  : free_control_scope.
Notation "p ;; q" :=
  (bind p (fun _ => q)) (at level 100, right associativity)
  : free_control_scope.
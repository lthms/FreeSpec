Set Universe Polymorphism.

Require Import Coq.Classes.Equivalence.

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

Notation "f <<< g" := (compose g f) (at level 50).
Notation "f >>> g" := (compose f g) (at level 50).

Definition function_weq
           {a b: Type}
          `{WEq b}
           (f g: a -> b)
  : Prop :=
  forall (x: a), f x == g x.

Lemma function_weq_refl
      {a b: Type}
     `{WEq b}
      (f: a -> b)
  : function_weq f f.
Proof.
  intro x.
  reflexivity.
Qed.

Lemma function_weq_sym
      {a b: Type}
     `{WEq b}
      (f g: a -> b)
  : function_weq f g
    -> function_weq g f.
Proof.
  unfold function_weq.
  intros H' x.
  rewrite H'.
  reflexivity.
Qed.

Lemma function_weq_trans
      {a b: Type}
     `{WEq b}
      (f g h: a -> b)
  : function_weq f g
    -> function_weq g h
    -> function_weq f h.
Proof.
  unfold function_weq.
  intros F G x.
  rewrite <- (G x).
  exact (F x).
Qed.

Add Parametric Relation
    (a b: Type)
   `{WEq b}
  : (a -> b) (function_weq)
    reflexivity  proved by function_weq_refl
    symmetry     proved by function_weq_sym
    transitivity proved by function_weq_trans
      as function_web_equiv.

Instance function_WEq
         (a b: Type)
        `{WEq b}
  : WEq (a -> b) :=
  { weq := function_weq
  }.

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
                                    (u:     a -> b)
                                    (v:     b -> c)
                                    (x:     f a)
       : map (u <<< v) x == ((map u) <<< (map v)) x
     }.

Arguments map [f _ a b] (_ _).
Arguments functor_identity [f _ a _] (x).
Arguments functor_composition_identity [f _ a b c _] (u v x).

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
     ; apply_associative_composition: forall {a b c: Type}
                                            `{WEq c}
                                             (u: f (b -> c))
                                             (v: f (a -> b))
                                             (w:   f a),
         compose <$> u <*> v <*> w == u <*> (v <*> w)
     }.

Arguments apply [f _ a b] (_ _).
Arguments apply_associative_composition [f _ a b c _] (u v w).

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
     }.

Arguments pure [f _ a] (x).
Arguments applicative_identity [f _ a _] (v).
Arguments applicative_composition [f _ a b c _] (u v w).
Arguments applicative_homomorphism [f _ a b _] (v x).
Arguments applicative_interchange [f _ a b _] (u y).

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
                                 `{WEq c}
                                  (f:     m a)
                                  (g:     a -> m b)
                                  (h:     b -> m c),
         (f >>= g) >>= h == f >>= (fun x => (g x) >>= h)
     }.

Arguments bind [m _ a b] (f g).
Arguments bind_associativity [m _ a b c _] (f g h).

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
                                  `{WEq b}
                                   (x:   a)
                                   (f:   a -> m b),
         pure x >>= f == f x
     ; monad_right_identity: forall {a: Type}
                                   `{WEq a}
                                    (x: m a),
         x >>= (fun y => pure y) == x
     }.

Arguments monad_left_identity [m _ a b _] (x f).
Arguments monad_right_identity [m _ a _] (x).

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

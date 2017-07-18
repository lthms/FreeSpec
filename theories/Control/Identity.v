Require Import FreeSpec.Control.
Require Import FreeSpec.WEq.

Definition Identity
           (a: Type)
  := a.

Instance identity_WEq
         (a: Type)
  : WEq (Identity a) :=
  { weq := eq
  }.

(** * Functor

 *)

Definition identity_map
           (a b: Type)
           (f:   a -> b)
           (x:   Identity a)
  : Identity b :=
  f x.

Instance identity_Functor
  : Functor Identity :=
  { map := identity_map
  }.
Proof.
  + reflexivity.
  + reflexivity.
Defined.

Definition identity_apply
           (a b: Type)
           (f:   Identity (a -> b))
           (x:   Identity a)
  : Identity b :=
  f x.

Instance identity_Apply
  : Apply Identity :=
  { apply := identity_apply
  }.

Definition identity_pure
           (a: Type)
           (x: a)
  : Identity a :=
  x.

Instance identity_Applicative
  : Applicative Identity :=
  { pure := identity_pure
  }.

Definition identity_bind
           (a b: Type)
           (x:   Identity a)
           (f:   a -> Identity b)
  : Identity b :=
  f x.

Instance identity_Bind
  : Bind Identity :=
  { bind := identity_bind
  }.
Proof.
  + reflexivity.
Defined.

Instance identity_Monad
  : Monad Identity :=
  {
  }.
Proof.
  + reflexivity.
  + reflexivity.
Defined.

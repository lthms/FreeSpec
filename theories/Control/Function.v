Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import FreeSpec.Control.
Require Import FreeSpec.WEq.

Definition func (a b: Type) := a -> b.

Definition map_func
           {a b c: Type}
           (f:     b -> c)
           (g:     func a b)
  : func a c :=
  f >>> g.

Instance func_Functor
         (a: Type)
  : Functor (func a) :=
  { map := @map_func a
  }.
Proof.
  (* functor identity *)
  + reflexivity.
  (* functor composition *)
  + reflexivity.
Defined.

Definition func_apply
           (a b c: Type)
           (f:     func a (b -> c))
           (g:     func a b)
  : func a c :=
  fun (x: a)
  => f x (g x).

Definition func_pure
           {a b: Type}
           (x:   b)
  : func a b :=
  fun (_: a)
  => x.

Instance func_Applicative
         (a: Type)
  : Applicative (func a) :=
  { pure := @func_pure a
  ; apply := @func_apply a
  }.
Proof.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
Defined.

Definition func_bind
           {a b c: Type}
           (f:     func a b)
           (g:     b -> func a c)
  : func a c :=
  fun (x: a)
  => g (f x) x.

Instance func_Monad
         (a: Type)
  : Monad (func a) :=
  { bind := @func_bind a
  }.
Proof.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + intros b c H f g g' Heq.
    cbn.
    unfold function_weq, func_bind.
    intros x.
    apply Heq.
  + reflexivity.
Defined.
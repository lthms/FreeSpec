(* Coq Set-up *)

Generalizable All Variables.

(** * Coq Stdlib Notations *)

From Coq Require Export List RelationClasses Setoid Morphisms.
Import ListNotations.

Open Scope signature_scope.
Close Scope nat_scope.
Open Scope bool_scope.

From ExtLib Require Import Functor Applicative Monad.
Import FunctorNotation.
Import ApplicativeNotation.
Import MonadLetNotation.

Open Scope monad_scope.

From ExtLib Require Import Extras.
Import FunNotation.

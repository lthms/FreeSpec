(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

(** * Utils Functions *)

Definition when {m : Type -> Type} `{Monad m} (cond : bool) `(p : m a) : m unit :=
  if cond then (p;; pure tt) else pure tt.

(** * Tactics *)

From Coq Require Export Eqdep.

Ltac ssubst :=
  lazymatch goal with
| [ H : existT _ _ _ = existT _ _ _ |- _ ]
  => apply Eqdep.EqdepTheory.inj_pair2 in H; ssubst
| [ |- _] => subst
end.

(** * Notations *)

Declare Scope freespec_scope.
Delimit Scope freespec_scope with freespec.

Reserved Infix "===" (at level 70, no associativity).

Notation "m '~>' n" :=
  (forall (α : Type), m α -> n α)
    (at level 80, no associativity)
  : type_scope.

(** * Generalizable Functions Equality *)

Definition function_eq {a b} (r : b -> b -> Prop) (f g : a -> b) : Prop :=
  forall (x : a), r (f x) (g x).

#[program, export]
Instance function_eq_Equivalence a `(Equivalence b r)
  : @Equivalence (a -> b) (function_eq r).

Next Obligation.
  now intros f x.
Qed.

Next Obligation.
  intros f g equ x.
  symmetry.
  apply equ.
Qed.

Next Obligation.
  intros f g h equ1 equ2 x.
  transitivity (g x); [ apply equ1 | apply equ2 ].
Qed.

(** * Hint Databases *)

#[global] Create HintDb freespec.

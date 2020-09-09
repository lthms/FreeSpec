(** * Coq Set-up *)

#[global] Generalizable All Variables.

(** * Coq Stdlib Notations *)

From Coq Require Export List RelationClasses Setoid Morphisms.
Export ListNotations.

#[global] Open Scope signature_scope.
#[global] Close Scope nat_scope.
#[global] Open Scope bool_scope.


(** * ExtLib Notations *)

From ExtLib Require Export Functor Applicative Monad.
Export FunctorNotation.
Export ApplicativeNotation.
Export MonadLetNotation.

#[global] Open Scope monad_scope.

From ExtLib Require Export Extras.
Export FunNotation.

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

#[program]
Instance function_eq_Equivalence `(Equivalence b r)
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

#[global]
Create HintDb freespec.

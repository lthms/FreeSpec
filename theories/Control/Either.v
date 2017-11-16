Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.

Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Function.
Require Import FreeSpec.WEq.
Require Import FreeSpec.Newtype.

Local Open Scope free_weq_scope.

Inductive Either
          (L R:  Type)
  : Type :=
| left (x:  L)
  : Either L R
| right (y:  R)
  : Either L R.

Arguments left [L R] (x).
Arguments right [L R] (y).

Inductive either_weq
          {L R:  Type}
         `{WEq L}
         `{WEq R}
  : Either L R -> Either L R -> Prop :=
| weq_left (x y:  L)
           (Heq:  x == y)
  : either_weq (left x) (left y)
| weq_right (x y:  R)
            (Heq:  x == y)
  : either_weq (right x) (right y).

Fact either_weq_refl
     {L R:  Type} `{WEq L} `{WEq R}
     (x:    Either L R)
  : either_weq x x.
Proof.
  induction x; constructor; reflexivity.
Qed.

Fact either_weq_sym
     {L R:  Type} `{WEq L} `{WEq R}
     (x y:  Either L R)
  : either_weq x y
    -> either_weq y x.
Proof.
  intros Heq;
    destruct Heq as [x y Heq|x y Heq];
    symmetry in Heq;
    constructor;
    exact Heq.
Qed.

Fact either_weq_trans
     {L R:  Type} `{WEq L} `{WEq R}
     (x y z:  Either L R)
  : either_weq x y
    -> either_weq y z
    -> either_weq x z.
Proof.
  intros Heq1 Heq2.
  dependent induction Heq1;
    dependent induction Heq2;
    constructor;
    transitivity y;
    assumption.
  Qed.

Add Parametric Relation
    (L R:  Type) `{WEq L} `{WEq R}
  : (Either L R) either_weq
    reflexivity proved by either_weq_refl
    symmetry proved by either_weq_sym
    transitivity proved by either_weq_trans
      as either_relation.

Instance either_WEq
         (L R:  Type) `{WEq L} `{WEq R}
  : WEq (Either L R) | 1 :=
  { weq := either_weq
  }.

Definition either_map
           (L A B:  Type)
           (f:      A -> B)
           (x:      Either L A)
  : Either L B :=
  match x with
  | right x
    => right (f x)
  | left x
    => left x
  end.

Instance either_Functor
         (L:  Type) `{WEq L}
  : Functor (Either L) :=
  { map := @either_map L
  }.
Proof.
+ intros A Ha x.
  induction x; reflexivity.
+ intros A B C Hc u v x.
  induction x; reflexivity.
Defined.

Definition either_pure
           (L A:  Type)
           (x:    A)
  : Either L A :=
  right x.

Definition either_app
           (L A B:  Type)
           (fe:     Either L (A -> B))
           (x:      Either L A)
  : Either L B :=
  match fe, x with
  | right f, right x
    => right (f x)
  | left e, _ | _, left e
    => left e
  end.

Instance either_Applicative
         (L:  Type) `{WEq L}
  : Applicative (Either L) :=
  { pure := @either_pure L
  ; apply := @either_app L
  }.
Proof.
  + intros A Ha x.
    induction x; reflexivity.
  + intros A B C Hc u v w.
    induction u; induction v; induction w; reflexivity.
  + intros A B Ha v x.
    reflexivity.
  + intros A B Hb u y.
    induction u; reflexivity.
  + intros A B Hb g [x|x]; reflexivity.
Defined.

Definition either_bind
           (L A B:  Type)
           (x:      Either L A)
           (f:      A -> Either L B)
  : Either L B :=
  match x with
  | right x
    => f x
  | left x
    => left x
  end.

Instance either_Monad
         (L:  Type) `{WEq L}
  : Monad (Either L) :=
  { bind := either_bind L
  }.
Proof.
  + intros A B Hb x f; reflexivity.
  + intros A Ha [x|x]; reflexivity.
  + intros A B C Hc [f|f] g h; reflexivity.
  + intros A B Hb [x|x] f f' Heq.
    ++ reflexivity.
    ++ cbn.
       apply Heq.
  + intros A B Hb [x|x] f; reflexivity.
Defined.

(** * Why not [EitherT]

    Because of the definition of [EitherT m] (it is basically a
    wrapper arround [m (Either)]), we cannot prove the functor laws
    (and probably the other laws too).

    In order to be able to prove these laws, we need an additionnal
    law that tells [map f] is a morphism as long as [f] is a
    morphism. This works pretty great with all monads defined in
    [FreeSpec.Control], expect... [Program] (which is
    unfortunate). The reason is the definition of the [Program] [WEq]
    instance is too strong and require the results of the realization
    of two equivalent programs to be equal, not equivalent.

    It is not clear how hard it would be to fix that, so for now we
    have an ad-hoc solution. See the [FreeSpec.Fail] library for more
    information about that. It basically provides the necessary tools
    to promote an Interface so that the Interpreter may fail. It also
    provides a specific monad called [FailProgram] to deal with the
    errors in a transparent manner.
 *)
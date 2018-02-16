Require Import FreeSpec.Interface.
Require Import FreeSpec.OneOf.
Require Import FreeSpec.Control.
Require Import FreeSpec.Program.

Require Import Coq.Lists.List.

Local Open Scope free_control_scope.

Fixpoint specialize
         (x:    Type)
         (row:  list (Type -> Type))
  : list Type :=
  match row with
  | i :: rest
    => i x :: specialize x rest
  | nil
    => nil
  end.

Inductive row
          (set:  list (Type -> Type))
          (a:    Type)
  : Type :=
| Row (e:  oneOf (specialize a set))
  : row set a.

Class HasEffect
      (set:  list (Type -> Type))
      (I:    Type -> Type)
  := { contains_effects :> forall (r:  Type),
           Contains (I r) (specialize r set)
     }.

Instance HasEffect_head
         (set:  list (Type -> Type))
         (I:    Type -> Type)
  : HasEffect (I :: set) I :=
  {}.

Instance HasEffect_tail
         (set:  list (Type -> Type))
         (I:    Type -> Type)
         (H:    HasEffect set I)
         (any:  Type -> Type)
  : HasEffect (any :: set) I :=
  {}.

Definition inj_effect
           {a:    Type}
           {I:    Type -> Type}
           {set:  list (Type -> Type)} `{HasEffect set I}
           (x:    I a)
  : Program (row set) a :=
  Request (Row set a (inj (set := specialize a set) x)).

Section EXAMPLE.
  Inductive E1
  : Type -> Type :=
  | e1
    : E1 nat.

  Inductive E2
    : Type -> Type :=
  | e2 (x:  nat)
    : E2 unit.

  Definition my_program
             {set:  list (Type -> Type)}
            `{HasEffect set E1}
            `{HasEffect set E2}
    : Program (row set) unit :=
    x <- inj_effect e1;
    inj_effect (e2 x).
End EXAMPLE.
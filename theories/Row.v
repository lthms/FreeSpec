Require Import FreeSpec.Interface.
Require Import FreeSpec.Open.
Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Option.
Require Import FreeSpec.Program.
Require Import FreeSpec.Semantics.

Require Import Coq.Lists.List.

Local Open Scope free_control_scope.

Polymorphic Fixpoint getr
            (set:  list (Type -> Type))
            (n:    nat)
            {struct n}
  : Type -> Type :=
  match n, set with
  | 0, t :: _
    => t
  | S n, _ :: set'
    => getr set' n
  | _, _
    => fun _ => inhabited
  end.

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

Fixpoint generalize
         (x:    (Type -> Type) -> Type)
         (row:  list (Type -> Type))
  : list Type :=
  match row with
  | i :: rest
    => x i :: generalize x rest
  | nil
    => nil
  end.

Inductive row
          (set:  list (Type -> Type))
          (a:    Type)
  : Type :=
| Row (e:  union (specialize a set))
  : row set a.

Arguments Row [set a] (e).

Class HasEffect
      (set:  list (Type -> Type))
      (I:    Type -> Type)
  := { contains_spec :> forall (r:  Type),
           Contains (I r) (specialize r set)
     ; contains_gen :> forall (f: (Type -> Type) -> Type),
           Contains (f I) (generalize f set)
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
  Request (Row (inj (set := specialize a set) x)).

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

Fact get_spec_getr_eq
     (set:  list (Type -> Type))
     (a:    Type)
     (n:    nat)
  : get (specialize a set) n = (getr set n) a.
Proof.
  revert n.
  induction set; intros n.
  + cbn.
    induction n; reflexivity.
  + induction n; [ reflexivity |].
    cbn in *.
    apply IHset.
Qed.

Instance HasEffect_indexed
         (set:  list (Type -> Type))
         (n:    nat)
  : HasEffect set (getr set n) :=
  {}.
Admitted.

Definition semanticsRowSteps
           (set:   list (Type -> Type))
  : @PS (row set) (product (generalize Semantics set)).
  unfold PS.
  intros a sems e.
  refine (
      match e with
      | Row (OneOf n Ht x)
        => _
      end
    ).
  rewrite get_spec_getr_eq in Ht.
  subst.
  exact (visit sems (fun s => handle s x)).
Defined.

Definition mkSemanticsForRow
           {set:  list (Type -> Type)}
           (sems:  product (generalize Semantics set))
  : Semantics (row set) :=
  mkSemantics (semanticsRowSteps set) sems.
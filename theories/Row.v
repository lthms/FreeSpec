Require Import FreeSpec.Interface.
Require Import FreeSpec.Open.
Require Import FreeSpec.Control.
Require Import FreeSpec.Program.
Require Import FreeSpec.Semantics.
Require Import Omega.

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

Lemma specialize_length
      (x:    Type)
      (row:  list (Type -> Type))
  : length row = length (specialize x row).
Proof.
  induction row.
  + reflexivity.
  + cbn.
    rewrite IHrow.
    reflexivity.
Defined.

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

Lemma generalize_length
      (x:    (Type -> Type) -> Type)
      (row:  list (Type -> Type))
  : length row = length (generalize x row).
Proof.
  induction row.
  + reflexivity.
  + cbn.
    rewrite IHrow.
    reflexivity.
Defined.

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

Fact get_gen_getr_eq
     (set:  list (Type -> Type))
     (f:    (Type -> Type) -> Type)
     (n:    nat)
     (H:    n < length set)
  : get (generalize f set) n = f (getr set n).
Proof.
  revert H.
  revert n.
  induction set; intros n H.
  + cbn in H.
    omega.
  + induction n.
    ++ reflexivity.
    ++ cbn.
       cbn in IHn.
       rewrite IHset; [ reflexivity |].
       cbn in H.
       omega.
Defined.

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
Defined.

Instance HasEffect_indexed
         (set:  list (Type -> Type))
         (n:    nat)
         (H:    n < length set)
  : HasEffect set (getr set n) :=
  {}.
+ intros r.
  rewrite <- get_spec_getr_eq.
  apply Contains_nat.
  rewrite <- specialize_length.
  exact H.
+ intros f.
  rewrite <- get_gen_getr_eq; [| apply H ].
  apply Contains_nat.
  rewrite <- generalize_length.
  exact H.
Defined.

Definition semanticsRowSteps
           (set:   list (Type -> Type))
  : @PS (row set) (product (generalize Semantics set)).
  unfold PS.
  intros a sems e.
  refine (
      match e with
      | Row (OneOf n Ht Hb x)
        => _
      end
    ).
  rewrite <- specialize_length in Hb.
  rewrite get_spec_getr_eq in Ht.
  subst.
  refine (visit sems (fun s => handle s x)).
  apply HasEffect_indexed.
  exact Hb.
Defined.

Definition mkSemanticsForRow
           {set:  list (Type -> Type)}
           (sems:  product (generalize Semantics set))
  : Semantics (row set) :=
  mkSemantics (semanticsRowSteps set) sems.

Definition push_sem
           {eff:   list (Type -> Type)}
           {I:     Type -> Type}
           (sem:   Semantics I)
           (sems:  product (generalize Semantics eff))
  : product (generalize Semantics (I :: eff)) :=
  Acons sem sems.

Definition sem_nil
  : product (generalize Semantics nil) :=
  Anil.

Notation "<< x >>" :=
  (Acons x Anil)
  : free_row_scope.
Notation "<< x ; y ; .. ; z >>" :=
  (Acons x (Acons y .. (Acons z Anil) ..))
  : free_row_scope.

Notation "<| x |>" := (mkSemanticsForRow (push_sem x sem_nil)) (only parsing) : free_row_scope.
Notation "<| x ; y ; .. ; z |>" := (mkSemanticsForRow (push_sem x (push_sem y .. (push_sem z sem_nil) ..))) (only parsing) : free_row_scope.
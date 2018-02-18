Require Import FreeSpec.Interface.
Require Import FreeSpec.Open.
Require Import FreeSpec.Control.
Require Import FreeSpec.Program.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Specification.

Require Import Omega.

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.

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

Polymorphic Fixpoint specialize
            (x:    Type)
            (row:  list (Type -> Type))
  : list Type :=
  match row with
  | i :: rest
    => i x :: specialize x rest
  | nil
    => nil
  end.

Lemma specialize_cardinal
      (x:    Type)
      (row:  list (Type -> Type))
  : cardinal row = cardinal (specialize x row).
Proof.
  induction row.
  + reflexivity.
  + cbn.
    rewrite IHrow.
    reflexivity.
Defined.

Polymorphic Fixpoint generalize
            (x:    (Type -> Type) -> Type)
            (row:  list (Type -> Type))
  : list Type :=
  match row with
  | i :: rest
    => x i :: generalize x rest
  | nil
    => nil
  end.

Lemma generalize_cardinal
      (x:    (Type -> Type) -> Type)
      (row:  list (Type -> Type))
  : cardinal row = cardinal (generalize x row).
Proof.
  induction row.
  + reflexivity.
  + cbn.
    rewrite IHrow.
    reflexivity.
Defined.

Polymorphic Inductive row
            (set:  list (Type -> Type))
            (a:    Type)
  : Type :=
| Row (e:  union (specialize a set))
  : row set a.

Arguments Row [set a] (e).

Polymorphic Class HasEffect
            (set:  list (Type -> Type))
            (I:    Type -> Type)
  := { contains_spec :> forall (r:  Type),
           Contains (I r) (specialize r set)
     ; contains_gen :> forall (f: (Type -> Type) -> Type),
           Contains (f I) (generalize f set)
     }.

Polymorphic Instance HasEffect_head
            (set:  list (Type -> Type))
            (I:    Type -> Type)
  : HasEffect (I :: set) I :=
  {}.

Polymorphic Instance HasEffect_tail
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
     (H:    n < cardinal set)
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

Polymorphic Instance HasEffect_indexed
            (set:  list (Type -> Type))
            (n:    nat)
            (H:    n < cardinal set)
  : HasEffect set (getr set n) :=
  {}.
+ intros r.
  rewrite <- get_spec_getr_eq.
  apply Contains_nat.
  rewrite <- specialize_cardinal.
  exact H.
+ intros f.
  rewrite <- get_gen_getr_eq; [| apply H ].
  apply Contains_nat.
  rewrite <- generalize_cardinal.
  exact H.
Defined.

(** * Semantics
 *)

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
  rewrite <- specialize_cardinal in Hb.
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

(** * Specification
 *)

Polymorphic Fixpoint generalize'
            (f:      Type -> (Type -> Type) -> Type)
            (specs:  list Type)
            (row:    list (Type -> Type))
  : list Type :=
  match specs, row with
  | w :: rst, i :: rst'
    => f w i :: generalize' f rst rst'
  | _, _
    => nil
  end.

Lemma generalize_cardinal'
      (f:      Type -> (Type -> Type) -> Type)
      (specs:  list Type)
      (row:    list (Type -> Type))
      (H:      cardinal specs = cardinal row)
  : cardinal row = cardinal (generalize' f specs row).
Proof.
  revert H.
  revert row.
  induction specs.
  + auto.
  + intros row H.
    cbn.
    induction row.
    ++ reflexivity.
    ++ cbn.
       rewrite IHspecs; [ reflexivity |].
       cbn in H.
       omega.
Defined.

Lemma get_generalize_get_getr
      (eff:  list (Type -> Type))
      (ws:   list Type)
      (f:    Type -> (Type -> Type) -> Type)
      (n:    nat)
      (H:    cardinal ws = cardinal eff)
      (H':   n < cardinal eff)
  : get (generalize' f ws eff) n = f (get ws n) (getr eff n).
Proof.
  revert H H'.
  revert n.
  revert ws.
  induction eff.
  + cbn.
    intros ws n H F.
    omega.
  + intros ws n H H'.
    dependent induction ws; [ discriminate H |].
    clear IHws.
    induction n.
    ++ reflexivity.
    ++ cbn.
       apply IHeff.
       +++ cbn in H.
           apply Nat.succ_inj in H.
           exact H.
       +++ cbn in H'.
           apply lt_S_n in H'.
           exact H'.
Defined.

Polymorphic Definition abstract_step_row
            {ws:     list Type}
            {eff:    list (Type -> Type)}
            (H:      cardinal ws = cardinal eff)
            (specs:  product (generalize' Specification ws eff))
            (a:      Type)
            (e:      row eff a)
            (x:      a)
            (w:      product ws)
  : product ws.
  induction e as [[T n Heq Hb e]].
  assert (Hbe: n < cardinal eff). {
    rewrite <- specialize_cardinal in Hb.
    exact Hb.
  }
  assert (Hbw: n < cardinal ws). {
    rewrite H.
    exact Hbe.
  }
  assert (Hget: get (specialize a eff) n = getr eff n a) by apply get_spec_getr_eq.
  assert (Hs: n < cardinal (generalize' Specification ws eff)). {
    rewrite <- generalize_cardinal'.
    + exact Hbe.
    + exact H.
  }
  assert (spec_n: Specification (get ws n) (getr eff n)). {
    remember (fetch specs n Hs) as spec_n.
    refine (eq_rect (get (generalize' Specification ws eff) n) (fun X => X) spec_n (Specification (get ws n) (getr eff n)) _).
    apply (get_generalize_get_getr eff ws Specification n H).
    exact Hbe.
  }
  refine (swap w n _ _); [ rewrite H;
                           rewrite <- specialize_cardinal in Hb;
                           exact Hb
                         |].
  assert (wn: get ws n) by exact (fetch w n Hbw).
  refine (abstract_step spec_n (eq_rect T (fun X => X) e (getr eff n a) _) x wn).
  rewrite <- Hget.
  symmetry.
  exact Heq.
Defined.

Definition mkRowSpecs
           {eff:    list (Type -> Type)}
           {ws:     list Type}
           (H:      cardinal ws = cardinal eff)
           (specs:  product (generalize' Specification ws eff))
  : Specification (product ws) (row eff).
  refine (
      {| abstract_step := @abstract_step_row ws eff H specs
       |}
    ).
Abort.
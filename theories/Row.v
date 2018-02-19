(* FreeSpec
 * Copyright (C) 2018 ANSSI
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>.
 *)

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

Fixpoint getr
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

Instance HasEffect_indexed
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

Notation "<| x |>" :=
  (mkSemanticsForRow (push_sem x sem_nil)) (only parsing)
  : free_row_scope.
Notation "<| x ; y ; .. ; z |>" :=
  (mkSemanticsForRow (push_sem x (push_sem y .. (push_sem z sem_nil) ..))) (only parsing)
  : free_row_scope.

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

Definition get_spec_n
           {ws:     list Type}
           {eff:    list (Type -> Type)}
           (H:      cardinal ws = cardinal eff)
           (specs:  product (generalize' Specification ws eff))
           (n:      nat)
           (Hb:     n < cardinal eff)
  : Specification (get ws n) (getr eff n).
  assert (Hb': n < cardinal ws). {
    rewrite H.
    exact Hb.
  }
  assert (Hb'': n < cardinal (generalize' Specification ws eff)). {
    rewrite <- generalize_cardinal'.
    exact Hb.
    exact H.
  }
  remember (fetch specs n Hb'') as spec_n.
  refine (eq_rect (get (generalize' Specification ws eff) n) (fun X => X) spec_n (Specification (get ws n) (getr eff n)) _).
  apply (get_generalize_get_getr eff ws Specification n H).
  exact Hb.
Defined.

Definition abstract_step_row
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
  assert (spec_n: Specification (get ws n) (getr eff n))
    by exact (get_spec_n H specs n Hbe).
  refine (swap w n _ _); [ rewrite H;
                           rewrite <- specialize_cardinal in Hb;
                           exact Hb
                         |].
  assert (wn: get ws n) by exact (fetch w n Hbw).
  refine (abstract_step spec_n (eq_rect T (fun X => X) e (getr eff n a) _) x wn).
  rewrite <- get_spec_getr_eq.
  symmetry.
  exact Heq.
Defined.

Definition row_precondition
           {ws:     list Type}
           {eff:    list (Type -> Type)}
           (H:      cardinal ws = cardinal eff)
           (specs:  product (generalize' Specification ws eff))
           (a:      Type)
           (e:      row eff a)
           (w:      product ws)
  : Prop.
  induction e as [[T n Heq Hb e]].
  assert (Hbe: n < cardinal eff). {
    rewrite <- specialize_cardinal in Hb.
    exact Hb.
  }
  assert (Hbw: n < cardinal ws). {
    rewrite H.
    exact Hbe.
  }
  assert (wn: get ws n) by exact (fetch w n Hbw).
  assert (spec_n: Specification (get ws n) (getr eff n))
    by exact (get_spec_n H specs n Hbe).
  refine (precondition spec_n
                       (eq_rect T (fun X => X) e (getr eff n a) _)
                       wn).
  rewrite <- get_spec_getr_eq.
  symmetry.
  exact Heq.
Defined.

Definition row_postcondition
           {ws:     list Type}
           {eff:    list (Type -> Type)}
           (H:      cardinal ws = cardinal eff)
           (specs:  product (generalize' Specification ws eff))
           (a:      Type)
           (e:      row eff a)
           (x:      a)
           (w:      product ws)
  : Prop.
  induction e as [[T n Heq Hb e]].
  assert (Hbe: n < cardinal eff). {
    rewrite <- specialize_cardinal in Hb.
    exact Hb.
  }
  assert (Hbw: n < cardinal ws). {
    rewrite H.
    exact Hbe.
  }
  assert (wn: get ws n) by exact (fetch w n Hbw).
  assert (spec_n: Specification (get ws n) (getr eff n))
    by exact (get_spec_n H specs n Hbe).
  refine (postcondition spec_n
                        (eq_rect T (fun X => X) e (getr eff n a) _)
                        x
                        wn).
  rewrite <- get_spec_getr_eq.
  symmetry.
  exact Heq.
Defined.

Inductive SpecsBuilder
          (eff:  list (Type -> Type))
          (ws:   list Type) :=
  { specs:   product (generalize' Specification ws eff)
  ; card_p:  cardinal ws = cardinal eff
  }.

Arguments specs [eff ws] (_).
Arguments card_p [eff ws] (_).

Definition mkRowSpecs
           {eff:    list (Type -> Type)}
           {ws:     list Type}
           (build:  SpecsBuilder eff ws)
  : Specification (product ws) (row eff) :=
    {| abstract_step := @abstract_step_row ws eff (card_p build) (specs build)
     ; precondition  := @row_precondition ws eff (card_p build) (specs build)
     ; postcondition  := @row_postcondition ws eff (card_p build) (specs build)
    |}.

Definition nil_spec
  : SpecsBuilder nil nil :=
  {| specs := (Anil: product (generalize' Specification nil nil))
   ; card_p := eq_refl
  |}.

Definition push_spec
           {eff:   list (Type -> Type)}
           {i:     Type -> Type}
           {ws:    list Type}
           {w:     Type}
           (spec:  Specification w i)
           (prev:  SpecsBuilder eff ws)
  : SpecsBuilder (i :: eff) (w :: ws).
  refine (
      {| specs := (Acons spec (specs prev): product (generalize' Specification (w :: ws) (i :: eff)))
       |}
    ).
  destruct prev as [_H H].
  cbn.
  rewrite H.
  reflexivity.
Defined.

Notation "|< x >|" :=
  (mkRowSpecs ((push_spec x nil_spec))) (only parsing)
  : free_row_scope.
Notation "|< x ; y ; .. ; z >|" :=
  (mkRowSpecs (push_spec x (push_spec y .. (push_spec z nil_spec) ..))) (only parsing)
  : free_row_scope.
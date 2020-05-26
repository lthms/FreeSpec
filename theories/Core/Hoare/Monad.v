(* FreeSpec
 * Copyright (C) 2018–2020 ANSSI
 *
 * Contributors:
 * 2018–2020 Thomas Letan <thomas.letan@ssi.gouv.fr>
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

From Base Require Export Prelude.

(** * Definition *)

Record hoare (Σ : Type) (α : Type) : Type :=
  mk_hoare { pre : Σ -> Prop
           ; post : Σ -> α -> Σ -> Prop
           }.

Arguments mk_hoare {Σ α} (pre post).
Arguments pre {Σ α} (_ _).
Arguments post {Σ α} (_ _ _).

Definition hoare_pure {Σ α} (x : α) : hoare Σ α :=
  mk_hoare (fun _ => True) (fun s y s' => x = y /\ s = s').

Definition hoare_bind {Σ α β} (h : hoare Σ α) (k : α -> hoare Σ β) : hoare Σ β :=
  mk_hoare (fun s => pre h s /\ (forall x s', post h s x s' -> pre (k x) s'))
           (fun s x s'' => exists y s', post h s y s' /\ post (k y) s' x s'').

(** * Instances *)

(* TODO: use `begin details` when coq.8.12 is released *)
(* begin hide *)

(** Reasoning with the [hoare] type has proven to be cumbersome to say the
    least. However, one can use the automation features of Coq to ease the
    verification process.

    More precisely, we implement several “angry”, ad-hoc tactics. *)

Lemma iff_p_p (p : Prop) : (p <-> p) <-> True.

Proof.
  now split.
Qed.

Lemma prop_and_neutral (p : Prop) : (True /\ p) <-> p.

Proof.
  now repeat split.
Qed.

Lemma imply_true_true (p : Type) : (p -> True) <-> True.

Proof.
  now repeat split.
Qed.

Lemma and_imply_equ (p q r : Prop) : (p /\ q -> r) <-> (p -> q -> r).

Proof.
  split.
  + intros H hp hq.
    apply H.
    now split.
  + intros H [hp hq].
    now apply H.
Qed.

Lemma alias_equ {a} (x : a) (p : a -> Prop)
  : (forall (y : a), y = x -> p y) <-> p x.

Proof.
  split.
  + intros H.
    now apply (H x).
  + intros hx y equ.
    now rewrite equ.
Qed.

Lemma forall_equ_2 {a b} (x : a) (y : b) (p : a -> b -> Prop)
  : (forall (x' : a) (y' : b), x = x' -> y = y' -> p x' y') <-> p x y.

Proof.
  split.
  + intros H.
    now apply H.
  + intros hxy x' y' equ1 equ2.
    now subst.
Qed.

Lemma forall_equ_2' {a b} (x : a) (y : b) (p : a -> b -> Prop)
  : (forall (x' : a) (y' : b), x' = x -> y' = y -> p x' y') <-> p x y.

Proof.
  split.
  + intros H.
    now apply H.
  + intros hxy x' y' equ1 equ2.
    now subst.
Qed.

Lemma exists_equ_2 {a b} (x : a) (y : b) (p : a -> b -> Prop)
  : (exists (x' : a) (y' : b), (x = x' /\ y = y') /\ p x' y') <-> p x y.

Proof.
  split.
  + intros H.
    now destruct H as [x' [y' [[equ1 equ2] H]]]; subst.
  + intros hxy.
    exists x.
    exists y.
    now split.
Qed.

Lemma exists_equ_2' {a b} (x : a) (y : b) (p : a -> b -> Prop)
  : (exists (x' : a) (y' : b), (x' = x /\ y' = y) /\ p x' y') <-> p x y.

Proof.
  split.
  + intros H.
    now destruct H as [x' [y' [[equ1 equ2] H]]]; subst.
  + intros hxy.
    exists x.
    exists y.
    now split.
Qed.

Lemma eq_sym_equ {a} (x y : a) : x = y <-> y = x.

Proof.
  now repeat split.
Qed.

Ltac angry_rewrite :=
  repeat (
      setoid_rewrite prop_and_neutral
      || setoid_rewrite imply_true_true
      || setoid_rewrite (and_comm _ True)
      || setoid_rewrite (and_comm _ (_ /\ _))
      || setoid_rewrite and_imply_equ
      || setoid_rewrite forall_equ_2
      || setoid_rewrite exists_equ_2
      || setoid_rewrite exists_equ_2'
      || setoid_rewrite iff_p_p
    ).

Ltac angry_destruct H :=
  match type of H with
  | _ /\ _ => let H' := fresh "H" in
              let H'' := fresh "H" in
              destruct H as [H' H''];
              angry_destruct H';
              angry_destruct H''
  | exists _, _ => let x := fresh "x" in
                   let H' := fresh "H" in
                   destruct H as [x H']; angry_destruct H'
  | _ => idtac
  end.

Ltac angry_intros :=
  let H := fresh "H" in
  intros H; angry_destruct H.

Ltac angry_exists :=
  repeat (eexists; eauto).
(* end hide *)

(** ** [Equality] *)

Inductive hoare_eq {Σ α} (h1 h2 : hoare Σ α) : Prop :=
| mk_hoare_eq
    (pre_eq : forall s, pre h1 s <-> pre h2 s)
    (post_eq : forall s x s', post h1 s x s' <-> post h2 s x s')
  : hoare_eq h1 h2.

Lemma hoare_eq_refl {Σ α} (h : hoare Σ α) : hoare_eq h h.

Proof.
  easy.
Qed.

Lemma hoare_eq_sym {Σ α} (h1 h2 : hoare Σ α) : hoare_eq h1 h2 -> hoare_eq h2 h1.

Proof.
  intros equ.
  constructor;
    symmetry;
    apply equ.
Qed.

Lemma hoare_eq_trans {Σ α} (h1 h2 h3 : hoare Σ α)
    (equ_1_2 : hoare_eq h1 h2) (equ_2_3 : hoare_eq h2 h3)
  : hoare_eq h1 h3.

Proof.
  constructor.
  + intros s.
    transitivity (pre h2 s); [ apply equ_1_2 | apply equ_2_3 ].
  + intros s x s'.
    transitivity (post h2 s x s'); [ apply equ_1_2 | apply equ_2_3 ].
Qed.

#[refine]
Instance hoare_eq_Equivalence : Equivalence (@hoare_eq Σ α) := {}.

Proof.
  + intros h.
    apply hoare_eq_refl.
  + intros h h'.
    apply hoare_eq_sym.
  + intros h h' h''.
    apply hoare_eq_trans.
Qed.

Instance hoare_eq_EquProp : EquProp (@hoare Σ α) :=
  { equal := hoare_eq }.

#[program]
Instance hoare_eq_EquPropL : EquPropL (@hoare Σ α).

#[program]
Instance pre_Proper : Proper (equal ==> eq ==> iff) (@pre Σ α).

Next Obligation.
  add_morphism_tactic.
  intros h1 h2 equ s.
  apply equ.
Qed.

#[program]
Instance post_Proper : Proper (equal ==> eq ==> eq ==> eq ==> iff) (@post Σ α).

Next Obligation.
  add_morphism_tactic.
  intros h1 h2 equ s x s'.
  apply equ.
Qed.

(** ** [Functor] *)

Definition hoare_map {Σ α β} (f : α -> β) (h : hoare Σ α) : hoare Σ β :=
  hoare_bind h (fun x => hoare_pure (f x)).

Instance hoare_Functor : Functor (hoare Σ) :=
  { map := fun _ _ => hoare_map }.

#[refine]
Instance hoare_FunctorL : FunctorL (hoare Σ) := {}.

Proof.
  all: cbn; intros; (constructor; [ intros s; now cbn | ]).
  + intros s r s'.
    split; cbn.
    ++ now angry_rewrite.
    ++ now angry_rewrite.
  + intros s r s'.
    split; cbn.
    ++ angry_intros; subst.
       angry_rewrite.
       angry_exists.
    ++ angry_intros; subst.
       angry_exists.
Qed.

(** ** [Applicative] *)

Definition hoare_apply {Σ α β} (hf : hoare Σ (α -> β)) (h : hoare Σ α)
  : hoare Σ β :=
  hoare_bind hf (fun f => hoare_map f h).

Lemma hoare_apply_id `{EquProp α} {Σ} (v : hoare Σ α)
   : hoare_eq (hoare_apply (hoare_pure id) v) v.

Proof.
  constructor.
  all: intros; cbn ; now angry_rewrite.
Qed.

Lemma hoare_apply_compose `{EquProp γ} {Σ α β}
    (u : hoare Σ (β -> γ)) (v : hoare Σ (α -> β)) (w : hoare Σ α)
  : hoare_eq (hoare_apply (hoare_apply (hoare_apply (hoare_pure compose) u) v) w)
             (hoare_apply u (hoare_apply v w)).

Proof.
  constructor; intros; cbn.
  + angry_rewrite.
    rewrite and_assoc.
    rewrite <- (and_iff_compat_l (pre u s)); [ reflexivity | ].
    angry_rewrite.
    split.
    ++ intros; split.
       +++ intros.
           angry_destruct H1; subst.
           specialize (H0 x0 s' H3).
           now destruct H0 as [H0 _].
       +++ repeat angry_intros; subst.
           specialize (H0 x1 x0 H6).
           destruct H0 as [_ H0].
           eapply H0.
           exact H8.
    ++ intros [H1 H2] x s' q.
       split.
       +++ eapply H1.
           angry_exists.
       +++ intros f s'' q'.
           eapply H2.
           angry_exists.
  + angry_rewrite.
    split;
       intros Hex;
       angry_destruct Hex; subst;
       repeat (eexists; eauto).
Qed.

Lemma hoare_apply_pure {Σ α} `{EquProp β}
    (v : α -> β) (x : α)
  : hoare_eq (Σ := Σ) (hoare_apply (hoare_pure v) (hoare_pure x)) (hoare_pure (v x)).

Proof.
  constructor; cbn.
  angry_rewrite; auto.
  intros s y s'.
  split.
  + intros [f [s'' [[equ1 equ2] [z [s''' H1]]]]].
    now intuition; subst.
  + angry_intros; subst.
    angry_exists.
Qed.

Lemma hoare_pure_apply {Σ α} `{EquProp β}
    (u : hoare Σ (α -> β)) (y : α)
  : hoare_eq (hoare_apply u (hoare_pure y))
             (hoare_apply (hoare_pure (fun z => z y)) u).

Proof.
  constructor; cbn.
  + now angry_rewrite.
  + intros.
    split;
      angry_intros;
      subst;
      angry_exists.
Qed.

Lemma hoare_map_hoare_apply {Σ α} `{EquProp β}
    (g : α -> β) (x : hoare Σ α)
  : hoare_eq (hoare_map g x) (hoare_apply (hoare_pure g) x).

Proof.
  constructor; cbn; intros; now angry_rewrite.
Qed.

Instance hoare_Applicative : Applicative (hoare Σ) :=
  { apply := fun _ _ => hoare_apply
  ; pure := fun _ => hoare_pure
  }.

#[refine]
Instance hoare_ApplicativeL : ApplicativeL (hoare Σ) := {}.

Proof.
  all: cbn; intros.
  + apply hoare_apply_id.
  + apply hoare_apply_compose.
  + apply hoare_apply_pure.
  + apply hoare_pure_apply.
  + apply hoare_map_hoare_apply.
Qed.

(** ** [Monad] *)

Lemma hoare_bind_pure {Σ α} `{EquProp β} (x : α) (f : α -> hoare Σ β)
  : hoare_eq (hoare_bind (hoare_pure x) f) (f x).

Proof.
  constructor; cbn; intros; now angry_rewrite.
Qed.

Instance hoare_Monad : Monad (hoare Σ) :=
  { bind := fun _ _ => hoare_bind }.

#[refine]
Instance hoare_MonadL : MonadL (hoare Σ) := {}.

Proof.
  all: cbn; intros.
  + apply hoare_bind_pure.
  + constructor.
    ++ intros s.
       now cbn.
    ++ intros s r s'; cbn; split.
       +++ now angry_intros; subst.
       +++ repeat angry_intros; subst.
           angry_exists.
  + constructor.
    ++ intros s.
       split; cbn.
       +++ angry_intros.
           split; auto.
           intros x s' q.
           split; auto.
           intros t s'' q'.
           apply H1.
           angry_exists.
       +++ angry_intros.
           repeat (split; auto).
           ++++ intros x s' q.
                now apply H1.
           ++++ repeat angry_intros.
                eapply H1; eauto.
    ++ intros s x s'.
       cbn.
       split.
       +++ angry_intros.
           angry_exists.
       +++ angry_intros.
           angry_exists.
  + constructor.
    ++ intros s.
       cbn.
       setoid_rewrite H.
       reflexivity.
    ++ intros s r s'.
       cbn.
       setoid_rewrite H.
       reflexivity.
  + reflexivity.
Qed.

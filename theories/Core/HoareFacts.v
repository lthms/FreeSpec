(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From FreeSpec.Core Require Import Interface ImpureFacts Contract.
From FreeSpec.Core Require Export Hoare.

(** * Equivalence Relation *)

Inductive hoare_eq {Σ α} (h1 h2 : hoare Σ α) : Prop :=
| mk_hoare_eq
    (pre_eq : forall s, pre h1 s <-> pre h2 s)
    (post_eq : forall s x s', post h1 s x s' <-> post h2 s x s')
  : hoare_eq h1 h2.

#[program]
Instance hoare_Equivalence Σ α : @Equivalence (hoare Σ α) hoare_eq.

Next Obligation.
  easy.
Qed.

Next Obligation.
  intros h1 h2 equ.
  constructor;
    symmetry;
    apply equ.
Qed.

Next Obligation.
  intros h1 h2 h3 equ_1_2 equ_2_3.
  constructor.
  + intros s.
    transitivity (pre h2 s); [ apply equ_1_2 | apply equ_2_3 ].
  + intros s x s'.
    transitivity (post h2 s x s'); [ apply equ_1_2 | apply equ_2_3 ].
Qed.

(** * Proper Instances *)

#[program]
Instance pre_Proper Σ α : Proper (hoare_eq ==> eq ==> iff) (@pre Σ α).

Next Obligation.
  add_morphism_tactic.
  intros h1 h2 equ s.
  apply equ.
Qed.

#[program]
Instance post_Proper Σ α : Proper (hoare_eq ==> eq ==> eq ==> eq ==> iff) (@post Σ α).

Next Obligation.
  add_morphism_tactic.
  intros h1 h2 equ s x s'.
  apply equ.
Qed.

#[program]
Instance to_hoare_Proper ix i Ω c α MP
  : Proper (impure_eq ==> hoare_eq) (@to_hoare ix i MP Ω c α).

Next Obligation.
  add_morphism_tactic.
  intros p q equ.
  induction equ.
  + reflexivity.
  + constructor.
    ++ intros ω.
       cbn in *.
       setoid_rewrite H.
       reflexivity.
    ++ intros ω x ω'.
       cbn in *.
       setoid_rewrite H.
       reflexivity.
Qed.

(** * General Lemmas *)

Lemma to_hoare_step `{MayProvide ix i} `(c : contract i Ω)
   `(e : ix a) `(f : a -> impure ix a)
   `(hpre : pre (to_hoare c (request_then e f)) ω)
    (x : a) (step : gen_callee_obligation c ω e x)
  : pre (to_hoare c (f x)) (gen_witness_update c ω e x).

Proof.
  destruct hpre as [hbefore hafter].
  apply hafter.
  cbn.
  unfold gen_callee_obligation, gen_witness_update in *.
  now destruct proj_p.
Qed.

#[global] Hint Resolve to_hoare_step : freespec.

Lemma to_hoare_pre_bind_assoc `{MayProvide ix i} `(c : contract i Ω)
   `(p : impure ix a) `(Hp : pre (to_hoare c p) ω)
   `(f : a -> impure ix b)
    (run : forall (x : a) (ω' : Ω),
        post (to_hoare c p) ω x ω' -> pre (to_hoare c (f x)) ω')
  : pre (to_hoare c (p >>= f)) ω.

Proof.
  revert ω Hp run.
  induction p; intros ω Hp run.
  + now apply run.
  + cbn in Hp.
    destruct Hp as [He Hn].
    change (request_then e f0 >>= f)
      with (request_then e (fun x => f0 x >>= f)).
    split.
    ++ exact He.
    ++ intros x ω' Hpost.
       specialize Hn with x ω'.
       destruct Hpost.
       rewrite H2 in *.
       assert (Hpre : pre (to_hoare c (f0 x)) (gen_witness_update c ω e x))
         by now apply Hn.
       apply H0; [ apply Hpre |].
       intros y ω'' Hpost.
       apply run.
       cbn.
       exists x.
       exists ω'.
       split; [split |].
       +++ exact H1.
       +++ exact H2.
       +++ rewrite H2.
           exact Hpost.
Qed.

#[global] Hint Resolve to_hoare_pre_bind_assoc : freespec.

Lemma to_hoare_post_bind_assoc `{MayProvide ix i} `(c : contract i Ω)
   `(p : impure ix a) `(f : a -> impure ix b)
   `(Hp : post (to_hoare c (impure_bind p f)) ω x ω')
  : exists y ω'',
    post (to_hoare c p) ω y ω'' /\ post (to_hoare c $ f y) ω'' x ω'.

Proof.
  revert ω Hp.
  induction p; intros ω Hp.
  + now exists x0, ω.
  + destruct Hp as [y [ω'' [Hp1 Hp2]]].
    apply H0 in Hp2.
    destruct Hp2 as [z [ω''' [Hp2 Hp3]]].
    exists z, ω'''.
    split; [| apply Hp3].
    exists y, ω''.
    now split.
Qed.

#[global] Hint Resolve to_hoare_post_bind_assoc : freespec.

Lemma to_hoare_contractprod `{Provide ix i, Provide ix j}
   `(ci : contract i Ωi) `(cj : contract j Ωj)
   `(p : impure ix a)
   `(prei : pre (to_hoare ci p) ωi) `(prej : pre (to_hoare cj p) ωj)
  : pre (to_hoare (ci * cj) p) (ωi, ωj).

Proof.
  revert ωi prei ωj prej.
  induction p; intros ωi prei ωj prej.
  + auto.
  + destruct prei as [calleri Hcalleei].
    destruct prej as [callerj Hcalleej].
    split.
    ++ now split.
    ++ intros x [ωi' ωj'] [[calleei calleej] equωs].
       cbn in equωs.
       inversion equωs; subst.
       apply H3.
       +++ apply Hcalleei.
           now split.
       +++ apply Hcalleej.
           now split.
Qed.

#[global] Hint Resolve to_hoare_contractprod : freespec.

#[local] Open Scope freespec_scope.

Lemma contract_impl_pre `(c1 : contract i Ω1) `(c2 : contract i Ω2)
   `(equ : c1 >- c2) (ω1 : Ω1) (ω2 : Ω2) (sync : ciso equ ω1 ω2)
   `(p : impure i a)
  : pre (to_hoare c1 p) ω1 -> pre (to_hoare c2 p) ω2.

Proof.
  induction equ.
  revert ω1 ω2 sync.
  induction p; intros ω1 ω2 sync.
  + now split.
  + cbn.
    intros [ocaller onext].
    split.
    ++ now apply (caller_impl ω1 ω2 _ e).
    ++ intros x ω2' [callee equω2'].
       subst.
       apply H with (ω1:=witness_update c1 ω1 e x).
       +++ now apply witness_impl.
       +++ apply onext.
           split; auto.
           apply (callee_impl ω2 ω1 _ e x); auto.
Qed.

#[global] Hint Resolve contract_impl_pre : freespec.

Lemma contract_impl_post `(c1 : contract i Ω1) `(c2 : contract i Ω2)
   `(impl : c1 >- c2)
    (callee : contract_callee_impl c1 c2 (ciso impl))
    (ω1 ω1' : Ω1) (ω2 : Ω2)
    (sync : ciso impl ω1 ω2) `(p : impure i a) (x : a)
    (post1 : post (to_hoare c1 p) ω1 x ω1')
  : exists ω2', ciso impl ω1' ω2' /\ post (to_hoare c2 p) ω2 x ω2'.

Proof.
  induction impl.
  cbn in *.
  revert x ω1 ω1' ω2 sync post1.
  induction p; intros y ω1 ω1' ω2 sync post1.
  + destruct post1 as [xequ ω1equ].
    cbn.
    exists ω2.
    now subst.
  + cbn in post1.
    destruct post1 as [x [ω1'' [[ocallee owitness] post1]]].
    subst.
    apply H with (ω2 := witness_update c2 ω2 e x) in post1.
    ++ destruct post1 as [ω2' [iso'' post1]].
       exists ω2'.
       split; auto.
       cbn.
       exists x, (witness_update c2 ω2 e x).
       repeat split; auto.
       apply (callee ω1 ω2 _ e x); auto.
    ++ now apply witness_impl.
Qed.

#[global] Hint Resolve contract_impl_post : freespec.

Lemma contract_strong_impl_post `(c1 : contract i Ω1) `(c2 : contract i Ω2)
    (simpl : c1 >>- c2)
    (ω1 ω1' : Ω1) (ω2 : Ω2)
    (sync : ciso simpl ω1 ω2) `(p : impure i a) (x : a)
    (post1 : post (to_hoare c1 p) ω1 x ω1')
  : exists ω2', ciso simpl ω1' ω2' /\ post (to_hoare c2 p) ω2 x ω2'.

Proof.
  eapply contract_impl_post; eauto.
  induction simpl.
  apply callee_strong_impl.
Qed.

#[global] Hint Resolve contract_strong_impl_post : freespec.

Lemma contract_equ_post `(c1 : contract i Ω1) `(c2 : contract i Ω2)
   `(equ : contract_equ c1 c2) (ω1 ω1' : Ω1) (ω2 : Ω2)
    (sync : ciso equ ω1 ω2) `(p : impure i a) (x : a)
    (post1 : post (to_hoare c1 p) ω1 x ω1')
  : exists ω2', ciso equ ω1' ω2' /\ post (to_hoare c2 p) ω2 x ω2'.

Proof.
  eapply contract_impl_post; eauto.
  clear ω1 ω1' ω2 post1 sync a p x.
  induction equ.
  induction impl1; induction impl2.
  cbn in *.
  intros ω1 ω2 a p x is_iso ocallee.
  apply (callee_impl0 ω1 ω2); auto.
  now apply iso_equ.
Qed.

#[global] Hint Resolve contract_equ_post : freespec.

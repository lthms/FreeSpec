Require Import Omega.

Lemma sub_0_r: forall n : nat, n - 0 = n.
  induction n; reflexivity.
Defined.

Lemma succ_0_l: forall n : nat, 0 + n = n.
  induction n; reflexivity.
Defined.

Lemma succ_inj_wd
      (n m: nat)
  : S n = S m <-> n = m.
Proof.
  split.
  + intro Heq.
    inversion Heq.
    reflexivity.
  + intros Heq; rewrite Heq; reflexivity.
Defined.

Lemma add_0_l
      (n: nat)
  : 0 + n = n.
Proof.
  cbn.
  reflexivity.
Defined.

Lemma add_0_r
      (n: nat)
  : n + 0 = n.
Proof.
  induction n.
  + reflexivity.
  + cbn.
    rewrite IHn.
    reflexivity.
Defined.

Lemma add_succ_comm
      (n m : nat)
  : S n + m = n + S m.
Proof.
  induction n.
  + cbn.
    reflexivity.
  + cbn.
    rewrite <- IHn.
    reflexivity.
Defined.

Lemma add_sym
      (n m: nat)
  : n + m = m + n.
Proof.
  induction n; destruct m.
  + reflexivity.
  + rewrite add_0_l.
    rewrite add_0_r.
    reflexivity.
  + rewrite add_0_l.
    rewrite add_0_r.
    reflexivity.
  + cbn.
    apply succ_inj_wd.
    rewrite IHn.
    rewrite add_succ_comm.
    reflexivity.
Defined.

Lemma sub_succ_r n m : n - (S m) = pred (n - m).
Proof.
  revert m.
  induction n;
    destruct m;
    simpl;
    auto.
  apply sub_0_r.
Defined.

Lemma add_succ_r
      (n m: nat)
  : S n + m = S (n + m).
Proof.
  cbn.
  reflexivity.
Defined.

Lemma add_succ_l
      (n m: nat)
  : n + S m = S (n + m).
Proof.
  induction n.
  + repeat rewrite add_0_l.
    reflexivity.
  + cbn.
    rewrite IHn.
    reflexivity.
Defined.

Lemma S_le_lt
      (n m: nat)
  : S n <= m
    -> n < m.
Proof.
  omega.
Defined.

Lemma add_pred_r: forall n m : nat, m <> 0 -> n + Nat.pred m = Nat.pred (n + m).
  induction n.
  intros.
  cbn.
  reflexivity.
  intros.
  cbn.
  rewrite IHn.
  cbn.
  induction m.
  destruct H.
  reflexivity.
  rewrite add_succ_l.
  cbn.
  reflexivity.
  exact H.
Defined.

Lemma add_sub_assoc
      (n m p: nat)
  : p <= m -> n + (m - p) = n + m - p.
Proof.
  revert m n.
  induction p.
  + intros n m Heq.
    rewrite sub_0_r.
    rewrite sub_0_r.
    reflexivity.
  + intros n m H.
    repeat rewrite sub_succ_r.
    rewrite <- IHp.
    rewrite add_pred_r.
    reflexivity.
    apply S_le_lt in H.
    apply Nat.sub_gt.
    exact H.
    apply le_Sn_le.
    exact H.
Defined.

Lemma sub_diag
      (n: nat)
  : n - n = 0.
Proof.
  induction n.
  + reflexivity.
  + cbn.
    rewrite IHn.
    reflexivity.
Defined.

Lemma sub_add: forall n m : nat, n <= m -> m - n + n = m.
Proof.
  intros n m H.
  rewrite add_sym.
  rewrite add_sub_assoc; [| exact H].
  rewrite add_sym.
  rewrite <- add_sub_assoc.
  rewrite (sub_diag n).
  rewrite add_0_r.
  reflexivity.
  apply le_n.
Defined.
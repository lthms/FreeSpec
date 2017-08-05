Require Import Omega.

Lemma le_refl
      (n: nat)
  : n <= n.
Proof.
  induction n.
  + constructor.
  + constructor.
Defined.

Lemma le_n_S
  : forall n m, n <= m -> S n <= S m.
Proof.
  induction 1; constructor; trivial.
Defined.

Lemma le_Sn_le (n m: nat)
  : S n <= m -> n <= m.
Proof.
  intros H.
  induction H.
  + constructor.
    constructor.
  + constructor.
    exact IHle.
Defined.

Lemma le_trans
      (p q r: nat)
  : p <= q -> q <= r -> p <= r.
Proof.
  intros H H'.
  induction H as [|n o].
  + apply H'.
  + apply IHo.
    apply le_Sn_le in H'.
    exact H'.
Defined.

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

Lemma sub_succ_l
      (n m: nat)
  : n <= m
    -> S m - n =  S (m - n).
Proof.
  revert m.
  induction n.
  + intros m H.
    induction m.
    ++ cbn.
       reflexivity.
    ++ cbn.
       reflexivity.
  + intros m H.
    assert (S m - n = S (m - n)). {
      apply le_Sn_le in H.
      apply IHn.
      exact H.
    }
    cbn.
    rewrite sub_succ_r.
    rewrite (S_pred (m - n) 0).
    cbn.
    reflexivity.
    omega.
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

Lemma add_assoc
      (n m p: nat)
  : n + (m + p) = (n + m) + p.
Proof.
  induction n.
  + cbn.
    reflexivity.
  + rewrite add_succ_r.
    rewrite IHn.
    cbn.
    reflexivity.
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
  apply le_refl.
Defined.

Lemma mul_0_r
      (n: nat)
  : n * 0 = 0.
Proof.
  induction n.
  + cbn.
    reflexivity.
  + cbn.
    rewrite IHn.
    reflexivity.
Defined.

Lemma mul_0_l
      (n: nat)
  : 0 * n = 0.
Proof.
  induction n.
  + cbn.
    reflexivity.
  + cbn.
    reflexivity.
Defined.

Lemma mul_sym
      (n m: nat)
  : n * m = m * n.
Proof.
  revert m.
  induction n.
  + intros m.
    cbn.
    rewrite mul_0_r.
    reflexivity.
  + intros m.
    cbn.
    rewrite IHn.
    rewrite add_sym.
    cbn.
    induction m.
    ++ cbn.
       reflexivity.
    ++ cbn.
       rewrite <- add_assoc.
       rewrite <- IHm.
       rewrite add_succ_l.
       rewrite add_succ_l.
       reflexivity.
Defined.

Lemma mul_sub_distr_r
      (n m p: nat)
  : (n - m) * p = n * p - m * p.
Proof.
  apply Nat.mul_sub_distr_r.
Defined.

Lemma mul_sub_distr_l
      (n m p: nat)
  : p * (n - m) = p * n - p * m.
Proof.
  apply Nat.mul_sub_distr_l.
Defined.

Lemma le_pred
      (n m: nat)
  : n <= m -> pred n <= pred m.
Proof.
  revert n.
  induction m.
  + intros.
    cbn.
    destruct n.
    ++ cbn.
       constructor.
    ++ inversion H.
  + intros.
    apply le_pred.
    exact H.
Defined.

Lemma le_S_n
      (n m: nat)
  : S n <= S m -> n <= m.
Proof.
  exact (le_pred (S n) (S m)).
Defined.

Lemma add_le_mono_l
      (n m p: nat)
  : n <= m -> p + n <= p + m.
Proof.
  revert n m.
  induction p.
  + intros n m H.
    cbn.
    exact H.
  + intros n m H.
    cbn.
    apply IHp in H.
    apply le_n_S in H.
    exact H.
Defined.

Lemma add_le_mono_r
      (n m p: nat)
  : n <= m -> n + p <= m + p.
Proof.
  rewrite (add_sym n p).
  rewrite (add_sym m p).
  apply add_le_mono_l.
Defined.

Lemma add_le_mono
      (n m p q: nat)
  : n <= m
    -> p <= q
    -> n + p <= m + q.
Proof.
  intros H1 H2.
  apply le_trans with (q:=m + p).
  + now apply add_le_mono_r.
  + now apply add_le_mono_l.
Defined.

Lemma le_0_le_minus
      (n m: nat)
  : n <= m -> 0 <= m - n.
Proof.
  revert m.
  induction n.
  + intros m H.
    rewrite sub_0_r.
    exact H.
  + intros m H.
    induction m.
    ++ apply Nat.nle_succ_0 in H.
       destruct H.
    ++ apply le_S_n in H.
       apply IHn in H.
       cbn.
       exact H.
Defined.

Lemma lt_0_lt_minus
      (n m: nat)
  : n < m -> 0 < m - n.
Proof.
  revert m.
  induction n.
  + intros m H.
    rewrite sub_0_r.
    exact H.
  + intros m H.
    induction m.
    ++ unfold lt in H.
       apply Nat.nle_succ_0 in H.
       destruct H.
    ++ apply lt_S_n in H.
       apply IHn in H.
       cbn.
       exact H.
Defined.

Lemma lt_mult
      (n m p: nat)
  : n < m -> (S p) * n < (S p) * m.
Proof.
  intros H.
  cbn.
  induction p.
  + cbn.
    repeat rewrite add_0_r.
    exact H.
  + cbn.
    apply Nat.add_lt_mono.
    ++ exact H.
    ++ exact IHp.
Defined.

Lemma le_mult
      (n m p: nat)
  : n <= m -> p * n <= p * m.
Proof.
  revert n m.
  induction p.
  + cbn.
    trivial.
  + intros n m H.
    cbn.
    assert (p * n <= p * m) by apply (IHp n m H).
    apply add_le_mono.
    ++ exact H.
    ++ exact H0.
Defined.

Lemma le_add_r
      (n m p: nat)
  : n <= m -> n + p <= m + p.
Proof.
  induction p.
  intros H.
  + repeat rewrite add_0_r.
    exact H.
  + intros.
    apply IHp in H.
    repeat rewrite add_succ_l.
    apply le_n_S.
    exact H.
Defined.

Lemma minus_minus_minus_add
      (n m p: nat)
  : n - m - p = n - (m + p).
Proof.
  induction p.
  + rewrite sub_0_r.
    rewrite add_0_r.
    reflexivity.
  + rewrite add_succ_l.
    repeat rewrite sub_succ_r.
    rewrite IHp.
    reflexivity.
Defined.

Lemma mul_2
      (p q: nat)
  : 2 * p - 2 * q = 2 * (p - q).
Proof.
  induction p.
  + cbn.
    reflexivity.
  + cbn.
    repeat rewrite add_0_r.
    induction q.
    ++ cbn.
       reflexivity.
    ++ cbn.
       omega.
Defined.

Lemma lt_power_2
      (x y: nat)
  : x < 2 ^ y
    -> S (x + x) < 2 ^ y + 2 ^ y.
Proof.
  intro H.
  assert (0 < 2 ^ y - x). {
    apply lt_0_lt_minus.
    exact H.
  }
  unfold lt in H0.
  assert (2 <= 2 ^ y + 2 ^ y - (x + x)). {
    assert (forall z, z + z = 2 * z). {
      intros z.
      cbn.
      rewrite add_0_r.
      reflexivity.
    }
    repeat rewrite H1.
    assert (2 = 2 * 1) by reflexivity.
    rewrite H2 at 1.
    rewrite mul_2.
    apply le_mult.
    exact H0.
  }
  apply le_add_r with (p:= x + x) in H1.
  rewrite sub_add in H1.
  cbn in H1.
  unfold lt.
  exact H1.
  apply le_mult with (p:=2) in H.
  cbn in H.
  repeat rewrite add_0_r in H.
  repeat rewrite add_succ_l in H.
  repeat apply le_Sn_le in H.
  exact H.
Defined.

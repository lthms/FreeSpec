Require Import Coq.Program.Program.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.

Inductive vector (A: Type) : nat -> Type :=
| vcons  {n:nat} : A -> vector A n -> vector A (S n)
| vnil : vector A 0.

Arguments vcons [A n] _ _.
Arguments vnil [A].

Program Fixpoint nth
        {A: Type}
        {n: nat}
        (v: vector A n)
        (i: nat)
        {struct v}
  : option A :=
  match v with
  | vcons x r => match i with
                 | 0 => Some x
                 | S i' => nth r i'
                 end
  | vnil => None
  end.

Definition vector_eq
           {A: Type}
           {n: nat}
           (v v': vector A n)
  : Prop :=
  forall (i: nat),
    nth v i = nth v' i.

Lemma vector_eq_refl
      {A: Type}
      {n: nat}
      (v: vector A n)
  : vector_eq v v.
Proof.
  intros i.
  reflexivity.
Qed.

Lemma vector_eq_sym
      {A: Type}
      {n: nat}
      (v v': vector A n)
  : vector_eq v v'
    -> vector_eq v' v.
Proof.
  unfold vector_eq.
  intros Heq i.
  rewrite (Heq i).
  reflexivity.
Qed.

Lemma vector_eq_trans
      {A: Type}
      {n: nat}
      (v v' v'': vector A n)
  : vector_eq v v'
    -> vector_eq v' v''
    -> vector_eq v v''.
Proof.
  unfold vector_eq.
  intros Heq Heq' i.
  rewrite (Heq i).
  rewrite (Heq' i).
  reflexivity.
Qed.

Add Parametric Relation
    (A: Type)
    (n: nat)
  : (vector A n) (vector_eq)
    reflexivity  proved by vector_eq_refl
    symmetry     proved by vector_eq_sym
    transitivity proved by vector_eq_trans
      as vector_eq_equiv.

Lemma nth_vcons
      {A: Type}
      {n: nat}
      (a a': A)
      (v v': vector A n)
  : (forall (i: nat), nth (vcons a v) (S i) = nth (vcons a' v') (S i))
    <-> vector_eq v v'.
Proof.
  split.
  + intros H.
    cbn in H.
    exact H.
  + intros Heq.
    cbn.
    exact Heq.
Qed.

Lemma eq_vcons
      {A: Type}
      {n: nat}
      (a a': A)
      (v v': vector A n)
  : vcons a v = vcons a' v' <-> a = a' /\ v = v'.
Proof.
  split.
  + intros Heq.
    inversion Heq.
    simpl_existT.
    split; [ reflexivity
           | exact H2
           ].
  + intros [Heq Heq'].
    rewrite Heq; rewrite Heq'.
    reflexivity.
Qed.

Lemma vector_eq_vcons
      {A: Type}
      {n: nat}
      (a a': A)
      (v v': vector A n)
  : vector_eq (vcons a v) (vcons a' v') <-> a = a' /\ vector_eq v v'.
Proof.
  split.
  + intros Heq.
    unfold vector_eq in Heq.
    assert (R: nth (vcons a v) 0 = nth (vcons a' v') 0) by apply (Heq 0).
    cbn in R.
    inversion R.
    split; [ reflexivity |].
    intros i.
    apply (Heq (S i)).
  + intros [Heq Heq'].
    intros i; induction i.
    ++ rewrite Heq; reflexivity.
    ++ cbn.
       apply (Heq' i).
Qed.

Lemma vector_eq_eq
      {A: Type}
      {n: nat}
      (v v': vector A n)
  : v = v' <-> vector_eq v v'.
Proof.
  split.
  + intros Heq.
    rewrite Heq.
    reflexivity.
  + intros Heq.
    dependent induction v';
      dependent induction v.
    ++ apply eq_vcons.
       apply vector_eq_vcons in Heq.
       destruct Heq as [H G].
       split; [ exact H
              | apply (IHv' v G)
              ].
    ++ reflexivity.
Qed.

Program Definition head
        {A: Type}
        {n: nat}
        (v: vector A (S n))
  : { a: A | nth v 0 = Some a } :=
  match v with
  | vcons a _ => a
  | vnil => !
  end.
Next Obligation.
  rewrite <- Heq_v.
  reflexivity.
Defined.

Program Fixpoint take
        {A:      Type}
        {n:      nat}
        (v:      vector A n)
        (e:      nat | e <= n)
        {struct v}
  : { v': vector A e | forall i : nat, i < e -> nth v' i = nth v i } :=
  match e with
  | 0 => vnil
  | S e' => match v with
            | vcons x r => vcons x (take r e')
            | vnil => !
            end
  end.
Next Obligation.
  apply (Nat.nlt_0_r i) in H.
  destruct H.
Defined.
Next Obligation.
  apply (le_S_n e' wildcard').
  exact H.
Defined.
Next Obligation.
  induction i.
  + reflexivity.
  + apply e0.
    apply lt_S_n in H.
    exact H.
Defined.
Next Obligation.
  apply Nat.nle_succ_0 in H.
  destruct H.
Defined.

Lemma sub_0_r: forall n : nat, n - 0 = n.
  induction n; reflexivity.
Defined.

Lemma succ_0_l: forall n : nat, 0 + n = n.
  induction n; reflexivity.
Defined.

Program Fixpoint drop
        {A:   Type}
        {n:   nat}
        (v:   vector A n)
        (b:   nat | b <= n)
  : { v': vector A (n - b) | forall i, i < n - b -> nth v' i = nth v (b + i) } :=
  match b with
  | 0 => v
  | S b' => match v with
            | vcons _ r => drop r b'
            | vnil => !
            end
  end.
Next Obligation.
  rewrite sub_0_r.
  reflexivity.
Defined.
Next Obligation.
  induction n;
    rewrite <- eq_rect_eq;
    reflexivity.
Defined.
Next Obligation.
  apply Nat.succ_le_mono.
  exact H.
Defined.
Next Obligation.
  apply Nat.nle_succ_0 in H.
  exact H.
Defined.

Program Definition extract
        {A:      Type}
        {n:      nat}
        (v:      vector A n)
        (e:      nat | e <= n)
        (b:      nat | b <= e)
  : { v': vector A (e - b) | forall i, i < (e - b) -> nth v' i = nth v (b + i) } :=
  take (drop v b) (e - b).
Next Obligation.
  transitivity e.
  + exact H.
  + exact H0.
Defined.
Next Obligation.
  apply Nat.sub_le_mono_r.
  exact H0.
Defined.
Next Obligation.
  destruct take; destruct drop.
  cbn in *.
  rewrite e0.
  + apply e1.
    assert (e - b <= n - b). {
      apply Nat.sub_le_mono_r.
      exact H1.
    }
    apply Nat.lt_le_trans with (m:=e - b).
    exact H.
    exact H2.
  + exact H.
Defined.

Program Fixpoint append
        {A:   Type}
        {n m: nat}
        (v:   vector A n)
        (v':  vector A m)
        {struct v}
  : { v'' : vector A (n + m) | forall i, (i < n -> nth v'' i = nth v i)
                                      /\ (n <= i -> nth v'' i = nth v' (i - n))} :=
  match v with
  | vnil => v'
  | vcons a v => vcons a (append v v')
  end.
Next Obligation.
  constructor.
  + omega.
  + intros H.
    rewrite <- minus_n_O.
    reflexivity.
Defined.
Next Obligation.
  cbn.
  induction i.
  + split.
    ++ reflexivity.
    ++ omega.
  + assert (G: (i < wildcard' -> nth x i = nth v i) /\
               (wildcard' <= i -> nth x i = nth v' (i - wildcard'))).
    apply (a0 i).
    destruct G as [X Y].
    split.
    ++ intros H.
       rewrite X.
       reflexivity.
       omega.
    ++ intros H.
       rewrite Y.
       rewrite Nat.sub_succ.
       reflexivity.
       omega.
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
  : n <= m -> S n - m = S (n - m).
Proof.
  revert n.
  induction m.
  + intros n H.
Admitted.

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
Admitted.

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

Program Definition set
        {A: Type}
        {n: nat}
        (m: nat | m <= n)
        (b: nat | m + b <= n)
        (v: vector A n)
        (v': vector A m)
  : { v'': vector A n |
      forall i, i < n
                -> (((i < b \/ i >= b + m)
                     -> nth v'' i = nth v i)
                    /\ ((i >= b /\ i < b + m)
                        -> nth v'' i = nth v' (i - b))) } :=
  append (append (take v b) v') (drop v (b + m)).
Next Obligation.
  rewrite add_sym in H.
  apply (Nat.le_le_add_le 0 m b n).
  apply Peano.le_0_n.
  rewrite (add_sym n).
  rewrite add_0_l.
  exact H.
Defined.
Next Obligation.
  rewrite add_sym.
  exact H.
Defined.
Next Obligation.
  rewrite add_sym.
  rewrite sub_add.
  + reflexivity.
  + rewrite add_sym.
    exact H.
Defined.
Next Obligation.
  cbn.
  destruct append.
  destruct append.
  destruct take.
  destruct drop.
  cbn in *.
  destruct sub_add.
  cbn in *.
  destruct add_sym.
  cbn in *.
  assert ((i < b -> nth x i = nth x1 i) /\ (b <= i -> nth x i = nth v' (i - b)))
    by apply (a i).
  assert ((i < b + m -> nth x0 i = nth x i) /\
          (b + m <= i -> nth x0 i = nth x2 (i - (b + m))))
    by (apply (a0 i)).
  destruct H2.
  destruct H3.
  split.
  + intros [X|Y].
    ++ rewrite <- e; [| exact X].
       rewrite <- H2; [| exact X].
       rewrite H3.
       +++ reflexivity.
       +++ Search (_ < _ -> _ < _ + _).
           apply (Nat.lt_lt_add_r i b m) in X.
           exact X.
    ++ rewrite H5.
       rewrite e0.
       assert (b + m + (i - (b + m)) = i) by omega.
       rewrite H6.
       reflexivity.
       omega.
       omega.
  + intros [X Y].
    rewrite H3; [| omega].
    rewrite <- H4; [| omega].
    reflexivity.
Defined.
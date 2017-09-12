Require Import Coq.Arith.Arith.
Require Import Coq.Program.Program.
Require Import Coq.Setoids.Setoid.
Require Import Omega.
Require Import FreeSpec.Control.

Require Import FreeSpec.Libs.OpenNat.OpenNat.
Require Import FreeSpec.PropBool.
Require Import FreeSpec.WEq.

(** * Definitions

 *)

Record mem
       (n: nat)
  : Type :=
  mkMem { mem_val: nat
        ; mem_bound: mem_val < 2 ^ n
        }.

Arguments mem_val [n] (_).
Arguments mem_bound [n] (_).

Definition byte := mem 8.
Definition word := mem 16.
Definition lword := mem 32.
Definition qword := mem 64.

Notation "x 'Byte'" := (x * 8) (at level 30, no associativity).
Notation "x 'Bytes'" := (x * 8) (at level 30, no associativity).

Inductive mem_eq
          {n:     nat}
          (m m':  mem n)
  : Prop :=
| mem_val_eq (H:  mem_val m = mem_val m')
  : mem_eq m m'.

Lemma mem_eq_refl
      {n: nat}
      (m: mem n)
  : mem_eq m m.
Proof.
  constructor.
  reflexivity.
Qed.

Lemma mem_eq_sym
      {n: nat}
      (m m': mem n)
  : mem_eq m m' -> mem_eq m' m.
Proof.
  intros [H].
  constructor.
  symmetry.
  exact H.
Qed.

Lemma mem_eq_trans
      {n: nat}
      (m m' m'': mem n)
  : mem_eq m m'
    -> mem_eq m' m''
    -> mem_eq m m''.
Proof.
  intros [H] [H'].
  constructor.
  transitivity (mem_val m').
  + exact H.
  + exact H'.
Qed.

Add Parametric Relation
    (n: nat)
  : (mem n) (@mem_eq n)
    reflexivity proved by mem_eq_refl
    symmetry proved by mem_eq_sym
    transitivity proved by mem_eq_trans
      as mem_eq_rel.

Instance mem_WEq
         (n: nat)
  : WEq (mem n) :=
  { weq := @mem_eq n
  }.

Definition mem_bool
           {n:     nat}
           (m m':  mem n)
  : bool :=
  Nat.eqb (mem_val m) (mem_val m').

Add Parametric Morphism
    (n:  nat)
  : mem_bool with signature (@mem_eq n) ==> (@mem_eq n) ==> eq
      as mem_bool_morphism.
  intros x x' [Heq] y y' [Heq'].
  unfold mem_bool.
  rewrite Heq; rewrite Heq'.
  reflexivity.
Qed.

Instance mem_bool_propbool
         (n:  nat)
  : PropBool2 (@mem_eq n) (@mem_bool n) :=
  {
  }.
Proof.
  intros m m'.
  split.
  + intro H.
    constructor.
    unfold mem_bool in H.
    apply (Nat.eqb_eq (mem_val m) (mem_val m')).
    exact H.
  + intros [H].
    unfold mem_bool.
    apply (Nat.eqb_eq (mem_val m) (mem_val m')).
    exact H.
Defined.

Instance mem_WEqBool
         (n:  nat)
  : WEqBool (mem n) :=
  { weq_bool := @mem_bool n
  }.

(** * Manipulation

    ** Boxing

 *)
Program Definition box
        (n x: nat)
  : mem n :=
  {| mem_val := x mod (2 ^ n)
   ; mem_bound := _
   |}.
Next Obligation.
  apply Nat.mod_upper_bound.
  apply Nat.pow_nonzero.
  intro H; discriminate.
Qed.

Definition zero
           (n: nat)
  : mem n :=
  box n 0.

(** ** Unboxing

 *)

Definition unbox
        {n: nat}
        (x: mem n)
  : nat :=
  mem_val x.

Add Parametric Morphism
    (n:  nat)
  : (@unbox n) with signature (@mem_eq n) ==> eq
      as unbox_morphism.
  intros x y [Heq].
  unfold unbox.
  exact Heq.
Qed.

Definition cast
           {n: nat}
           (m: nat)
           (x: mem n)
  : mem m :=
  box m (unbox x).

Add Parametric Morphism
    (n: nat)
    (m: nat)
  : (@cast n m)
    with signature (@mem_eq n) ==> eq
      as cast_morphism.
Proof.
  intros x y [H].
  unfold cast.
  unfold unbox.
  rewrite H.
  reflexivity.
Defined.

Lemma cast_same_size_eq
      {n: nat}
      (x: mem n)
  : mem_eq (cast n x) x.
Proof.
  unfold cast.
  unfold box.
  unfold unbox.
  constructor.
  destruct x as [x Hbound].
  cbn.
  apply Nat.mod_small.
  exact Hbound.
Qed.

Lemma cast_cast_is_cast
      {n m:  nat}
      (x:    mem n)
  : mem_eq (cast m (cast m x)) (cast m x).
Proof.
  unfold cast.
  unfold unbox.
  unfold box.
  destruct x.
  unfold mem_val.
  constructor.
  unfold mem_val.
  rewrite Nat.mod_mod; [ reflexivity |].
  apply Nat.pow_nonzero.
  intro H; discriminate.
Qed.

(** ** Arithmetic

 *)

Definition add
           {n: nat}
           (x y: mem n)
  : mem n :=
  box n (unbox x + unbox y).

Add Parametric Morphism
    (n: nat)
  : (@add n)
    with signature (@mem_eq n) ==> (@mem_eq n) ==> (@mem_eq n)
      as add_morphism.
Proof.
  intros m m' H p p' H'.
  unfold add.
  rewrite H.
  rewrite H'.
  reflexivity.
Defined.

Definition shiftl
           {n: nat}
           (x: mem n)
           (b: nat)
  : mem n :=
    box n (Nat.shiftl (unbox x) b).

Add Parametric Morphism
    (n: nat)
  : (@shiftl n)
    with signature (@mem_eq n) ==> eq ==> (@mem_eq n)
      as shiftl_morphism.
Proof.
  intros x y H z.
  unfold shiftl.
  rewrite H.
  reflexivity.
Defined.

Definition shiftr
           {n: nat}
           (x: mem n)
           (b: nat)
  : mem n :=
    box n (Nat.shiftr (unbox x) b).

Add Parametric Morphism
    (n: nat)
  : (@shiftr n)
    with signature (@mem_eq n) ==> eq ==> (@mem_eq n)
      as shiftr_morphism.
Proof.
  intros x y H z.
  unfold shiftr.
  rewrite H.
  reflexivity.
Defined.

Lemma shiftr_0_eq
      {n: nat}
      (x: mem n)
  : mem_eq (shiftr x 0) x.
Proof.
  unfold shiftr.
  cbn.
  fold (@cast n n x).
  apply cast_same_size_eq.
Qed.

Definition mle
           {n: nat}
           (x y: mem n)
  : Prop :=
  unbox x <= unbox y.

Definition mleb
           {n: nat}
           (x y: mem n)
  : bool :=
  unbox x <=? unbox y.

Definition mltb
           {n: nat}
           (x y: mem n)
  : bool :=
  unbox x <? unbox y.

(** * Manipulation

  *)

Definition append
           {n m:  nat}
           (v:    mem n)
           (v':   mem m)
  : mem (n + m) :=
  add (shiftl (cast (n + m) v') n)
      (cast (n + m) v).

Add Parametric Morphism
    (n m:  nat)
  : (@append n m) with signature mem_eq ==> mem_eq ==> mem_eq
      as append_morphism.
  intros x x' [Heq] y y' [Heq'].
  constructor.
  unfold append.
  unfold cast.
  unfold shiftl, add.
  unfold unbox, box.
  unfold mem_val.
  destruct   x   as [x  Hx];
    destruct x'  as [x' Hx'];
    destruct y   as [y  Hy];
    destruct y'  as [y' Hy'].
  cbn in *.
  subst.
  reflexivity.
Qed.

(** * Memory

 *)

Definition upper_half
           (n:  nat)
           (x:  mem (2 * n))
  : mem n :=
  cast n (shiftr x n).

Definition lower_half
           (n:  nat)
           (x:  mem (2 * n))
  : mem n :=
  cast n x.

Definition join
           (n:    nat)
           (h l:  mem n)
  : mem (2 * n) :=
  add (cast (2 * n) l) (shiftl (cast (2 * n) h) n).

Lemma pow_pos
      (a b:  nat)
  : 0 < a -> 0 < a ^ b.
Proof.
  intros H.
  apply neq_0_lt.
  apply Nat.neq_sym.
  eapply Nat.pow_nonzero.
  apply lt_0_neq in H.
  apply Nat.neq_sym.
  exact H.
Qed.

Lemma shiftr_reduces
      {n m:  nat}
  : Nat.shiftr n m <= n.
Proof.
  revert n.
  induction m.
  + cbn.
    reflexivity.
  + intros n.
    cbn.
    apply Nat.div2_decr.
    transitivity n.
    ++ apply IHm.
    ++ constructor.
       reflexivity.
Qed.

Lemma div2_prop
      (x r:  nat)
      (H:    x < 2 ^ r)
  : Nat.div2 x < 2 ^ Nat.pred r.
Proof.
  apply <- (Nat.mul_lt_mono_pos_l 2); [| omega ].
  apply (Nat.le_lt_trans (2 * Nat.div2 x) x).
  + transitivity (2 * Nat.div2 x + Nat.b2n (Nat.odd x)).
    ++ omega.
    ++ rewrite <- (Nat.div2_odd x).
       reflexivity.
  + induction r.
    ++ cbn in *.
       omega.
    ++ cbn.
       rewrite add_0_r.
       assert (Heq:  2 ^ r + 2 ^ r = 2 * (2 ^ r)) by omega.
       rewrite Heq.
       rewrite <- Nat.pow_succ_r.
       exact H.
       omega.
Qed.

Lemma shiftr_reduces'
      {x n m: nat}
      (H: x < 2 ^ n)
  : Nat.shiftr x m < 2 ^ (n - m).
Proof.
  revert x n H.
  induction m.
  + cbn.
    intros x n H.
    rewrite sub_0_r.
    exact H.
  + intros x n H.
    cbn.
    remember (Nat.shiftr x m) as x'.
    cbn in x'.
    assert (H':  Nat.shiftr x m < 2 ^ (n - m)). {
      apply IHm.
      exact H.
    }
    rewrite <- Heqx' in H'.
    rewrite Nat.sub_succ_r.
    remember (n - m) as r.
    apply div2_prop.
    exact H'.
Qed.

Lemma shiftl_shiftr_div
      (x n:  nat)
  : Nat.shiftl (Nat.shiftr x n) n = (2 ^ n) * (x / (2 ^ n)).
Proof.
  rewrite Nat.shiftr_div_pow2.
  rewrite Nat.shiftl_mul_pow2.
  apply Nat.mul_comm.
Qed.

Lemma shiftr_shiftl_le
      (x n:  nat)
  : Nat.shiftl (Nat.shiftr x n) n <= x.
Proof.
  rewrite shiftl_shiftr_div.
  remember (2 ^ n) as r.
  apply Nat.mul_div_le.
  induction n.
  + cbn in Heqr.
    rewrite Heqr.
    auto.
  + rewrite Heqr.
    apply Nat.neq_sym.
    apply lt_0_neq.
    apply pow_pos.
    repeat constructor.
Qed.

Lemma split_merge_eq
      (n: nat)
      (x: mem (2 * n))
  : mem_eq x (join n (upper_half n x) (lower_half n x)).
Proof.
  constructor.
  destruct x as [x Hx].
  unfold join, lower_half, upper_half, shiftl, shiftr, add, cast, box, unbox.
  unfold mem_val.
  rewrite (Nat.mod_small (x mod 2 ^ n) (2 ^ (2 * n))).
  + rewrite (Nat.mod_small ((Nat.shiftr x n mod 2 ^ (2 * n)) mod 2 ^ n) (2 ^ (2 * n))).
    ++ rewrite (Nat.mod_small (Nat.shiftr x n) (2 ^ (2 * n))).
       +++ rewrite (Nat.mod_small (Nat.shiftr x n) (2 ^ n)).
           ++++ rewrite (Nat.mod_small (Nat.shiftl (Nat.shiftr x n) n) (2 ^ (2 * n))); [| apply (Nat.le_lt_trans _ x); [| exact Hx ];
                                                                                          apply shiftr_shiftl_le
                                                                                       ].
                rewrite shiftl_shiftr_div.
                rewrite Nat.add_comm.
                rewrite <- Nat.div_mod.
                rewrite (Nat.mod_small _ _ Hx).
                reflexivity.
                apply Nat.neq_sym.
                apply lt_0_neq.
                apply pow_pos.
                omega.
           ++++ assert (Hhelper:  forall (a:  nat), 2 * a - a = a). {
                  clear Hx x n.
                  induction a.
                  + reflexivity.
                  + cbn.
                    rewrite add_0_r.
                    rewrite (Nat.add_comm a (S a)).
                    rewrite <- Nat.add_sub_assoc.
                    ++ rewrite Nat.sub_diag.
                       rewrite add_0_r.
                       reflexivity.
                    ++ constructor.
                }
                rewrite <- (Hhelper n) at 2.
                apply shiftr_reduces'.
                exact Hx.
       +++ apply (Nat.le_lt_trans _ x); [| exact Hx ].
           apply shiftr_reduces.
    ++ apply (Nat.lt_le_trans _ (2 ^ n)).
       +++ apply Nat.mod_bound_pos.
           apply le_0_n.
           apply pow_pos.
           auto.
       +++ apply Nat.pow_le_mono_r; omega.
  + apply (Nat.lt_le_trans (x mod (2 ^ n)) (2 ^ n)).
    ++ apply Nat.mod_bound_pos.
       apply le_0_n.
       apply pow_pos.
       auto.
    ++ apply Nat.pow_le_mono_r; omega.
Qed.

Program Definition split_word
        (x: word)
  : byte * byte :=
  (upper_half 8 x, lower_half 8 x).

Program Definition split_lword
        (x: lword)
  : byte * byte * byte * byte :=
  (fst (split_word (upper_half 16 x)),
   snd (split_word (upper_half 16 x)),
   fst (split_word (lower_half 16 x)),
   snd (split_word (lower_half 16 x))
   ).

Definition qfst
           {A B C D:  Type}
  : A * B * C * D -> A :=
  fst <<< fst <<< fst.

Definition qsnd
           {A B C D:  Type}
  : A * B * C * D -> B :=
  snd <<< fst <<< fst.

Definition qthrd
           {A B C D:  Type}
  : A * B * C * D -> C :=
  snd <<< fst.

Definition qlst
           {A B C D:  Type}
  : A * B * C * D -> D :=
  snd.
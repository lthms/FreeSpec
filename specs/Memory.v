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

Require Import Coq.NArith.NArith.
Require Import Coq.Program.Program.
Require Import Coq.Setoids.Setoid.
Require Import Omega.

Require Import FreeSpec.PropBool.
Require Import FreeSpec.WEq.

(** * Definitions

 *)

Local Close Scope nat_scope.
Local Open Scope N_scope.

Record mem
       (n: N)
  : Type :=
  mkMem { mem_val: N
        ; mem_bound: mem_val < 2 ^ n
        }.

Arguments mem_val [n] (_).
Arguments mem_bound [n] (_).

Definition byte := mem 8.
Definition word := mem 16.
Definition lword := mem 32.
Definition qword := mem 64.

Inductive mem_eq
          {n:     N}
          (m m':  mem n)
  : Prop :=
| mem_val_eq (H:  mem_val m = mem_val m')
  : mem_eq m m'.

Lemma mem_eq_refl
      {n: N}
      (m: mem n)
  : mem_eq m m.
Proof.
  constructor.
  reflexivity.
Qed.

Lemma mem_eq_sym
      {n: N}
      (m m': mem n)
  : mem_eq m m' -> mem_eq m' m.
Proof.
  intros [H].
  constructor.
  symmetry.
  exact H.
Qed.

Lemma mem_eq_trans
      {n: N}
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
    (n: N)
  : (mem n) (@mem_eq n)
    reflexivity proved by mem_eq_refl
    symmetry proved by mem_eq_sym
    transitivity proved by mem_eq_trans
      as mem_eq_rel.

Instance mem_WEq
         (n: N)
  : WEq (mem n) :=
  { weq := @mem_eq n
  }.

Definition mem_bool
           {n:     N}
           (m m':  mem n)
  : bool :=
  N.eqb (mem_val m) (mem_val m').

Add Parametric Morphism
    (n:  N)
  : mem_bool with signature (@mem_eq n) ==> (@mem_eq n) ==> eq
      as mem_bool_morphism.
  intros x x' [Heq] y y' [Heq'].
  unfold mem_bool.
  rewrite Heq; rewrite Heq'.
  reflexivity.
Qed.

Instance mem_bool_propbool
         (n:  N)
  : PropBool2 (@mem_eq n) (@mem_bool n) :=
  {
  }.
Proof.
  intros m m'.
  split.
  + intro H.
    constructor.
    unfold mem_bool in H.
    apply (N.eqb_eq (mem_val m) (mem_val m')).
    exact H.
  + intros [H].
    unfold mem_bool.
    apply (N.eqb_eq (mem_val m) (mem_val m')).
    exact H.
Defined.

Instance mem_WEqBool
         (n:  N)
  : WEqBool (mem n) :=
  { weq_bool := @mem_bool n
  }.

(** * Manipulation

    ** Boxing

 *)
Program Definition box
        (n x: N)
  : mem n :=
  {| mem_val := x mod (2 ^ n)
   ; mem_bound := _
   |}.
Next Obligation.
  apply N.mod_upper_bound.
  apply N.pow_nonzero.
  intro H; discriminate.
Qed.

(** ** Unboxing

 *)

Definition unbox
        {n: N}
        (x: mem n)
  : N :=
  mem_val x.

Add Parametric Morphism
    (n:  N)
  : (@unbox n) with signature (@mem_eq n) ==> eq
      as unbox_morphism.
  intros x y [Heq].
  unfold unbox.
  exact Heq.
Qed.

Definition cast
           {n: N}
           (m: N)
           (x: mem n)
  : mem m :=
  box m (unbox x).

Add Parametric Morphism
    (n: N)
    (m: N)
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
      {n: N}
      (x: mem n)
  : mem_eq (cast n x) x.
Proof.
  unfold cast.
  unfold box.
  unfold unbox.
  constructor.
  destruct x as [x Hbound].
  cbn.
  apply N.mod_small.
  exact Hbound.
Qed.

Lemma cast_cast_is_cast
      {n m:  N}
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
  rewrite N.mod_mod; [ reflexivity |].
  apply N.pow_nonzero.
  intro H; discriminate.
Qed.

(** ** Arithmetic

 *)

Definition add
           {n: N}
           (x y: mem n)
  : mem n :=
  box n (unbox x + unbox y).

Add Parametric Morphism
    (n: N)
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
           {n: N}
           (x: mem n)
           (b: N)
  : mem n :=
    box n (N.shiftl (unbox x) b).

Add Parametric Morphism
    (n: N)
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
           {n: N}
           (x: mem n)
           (b: N)
  : mem n :=
    box n (N.shiftr (unbox x) b).

Add Parametric Morphism
    (n:  N)
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
      {n: N}
      (x: mem n)
  : mem_eq (shiftr x 0) x.
Proof.
  unfold shiftr.
  cbn.
  fold (@cast n n x).
  apply cast_same_size_eq.
Qed.

Definition mle
           {n: N}
           (x y: mem n)
  : Prop :=
  unbox x <= unbox y.

Definition mleb
           {n: N}
           (x y: mem n)
  : bool :=
  unbox x <=? unbox y.

Definition mltb
           {n: N}
           (x y: mem n)
  : bool :=
  unbox x <? unbox y.

(** * Manipulation

  *)

Definition append
           {n m:  N}
           (v:    mem n)
           (v':   mem m)
  : mem (n + m) :=
  add (shiftl (cast (n + m) v') n)
      (cast (n + m) v).

Add Parametric Morphism
    (n m:  N)
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
           (n:  N)
           (x:  mem (2 * n))
  : mem n :=
  cast n (shiftr x n).

Add Parametric Morphism
    (n:  N)
  : (upper_half n) with signature (@mem_eq (2*n)) ==> (@mem_eq n)
      as upper_half_morphism.
Proof.
  intros [x Hx] [y Hy] [Heq].
  cbn in Heq.
  constructor.
  unfold upper_half, cast, shiftr, box, unbox.
  cbn.
  subst.
  reflexivity.
Qed.

Definition lower_half
           (n:  N)
           (x:  mem (2 * n))
  : mem n :=
  cast n x.

Add Parametric Morphism
    (n:  N)
  : (lower_half n) with signature (@mem_eq (2*n)) ==> (@mem_eq n)
      as lower_half_morphism.
Proof.
  intros [x Hx] [y Hy] [Heq].
  cbn in Heq.
  constructor.
  unfold lower_half, cast, shiftr, box, unbox.
  cbn.
  subst.
  reflexivity.
Qed.

Definition join
           (n:    N)
           (h l:  mem n)
  : mem (2 * n) :=
  add (cast (2 * n) l) (shiftl (cast (2 * n) h) n).

Add Parametric Morphism
    (n:  N)
  : (join n) with signature (@mem_eq n) ==> (@mem_eq n) ==> (@mem_eq (2*n))
      as join_morphism.
Proof.
  intros [x Hx] [y Hy] [Heq].
  intros [x' Hx'] [y' Hy'] [Heq'].
  cbn in *.
  constructor.
  unfold join, cast, shiftl, box, unbox.
  cbn.
  subst.
  reflexivity.
Qed.

Lemma pow_pos
      (a b:  N)
  : 0 < a -> 0 < a ^ b.
Proof.
  intros H.
  apply N.neq_0_lt_0.
  eapply N.pow_nonzero.
  apply N.neq_0_lt_0 in H.
  exact H.
Qed.

Lemma shiftr_reduces
      {n m:  N}
  : N.shiftr n m <= n.
Proof.
  revert n.
  induction m using N.peano_rect.
  + cbn.
    reflexivity.
  + intros n.
    cbn.
    rewrite N.shiftr_succ_r.
    transitivity (N.shiftr n m).
    ++ rewrite N.div2_div.
       apply N.div_le_upper_bound.
       +++ intro False.
           discriminate.
       +++ rewrite <- (N.mul_1_r (N.shiftr n m)) at 1.
           rewrite (N.mul_comm 2 _).
           apply N.mul_le_mono_nonneg_l; [ apply N.le_0_l
                                         | firstorder
                                         ].
           apply N.le_succ_diag_r.
    ++ apply IHm.
Qed.

Lemma div2_prop
      (x r:  N)
      (H:    x < 2 ^ r)
  : N.div2 x < 2 ^ N.pred r.
Proof.
  apply <- (N.mul_lt_mono_pos_l 2).
  + apply (N.le_lt_trans (2 * N.div2 x) x).
    ++ transitivity (2 * N.div2 x + N.b2n (N.odd x)).
       +++ apply N.le_add_r.
       +++ rewrite <- (N.div2_odd x).
           reflexivity.
    ++ induction r using N.peano_rect.
       +++ cbn in *.
           transitivity 1; [ exact H |].
           apply N.lt_1_2.
       +++ rewrite N.pred_succ.
           rewrite <- N.pow_succ_r.
           exact H.
           apply N.le_0_l.
  + exact N.lt_0_2.
Qed.

Lemma shiftr_reduces'
      {x n m: N}
      (H: x < 2 ^ n)
  : N.shiftr x m < 2 ^ (n - m).
Proof.
  revert x n H.
  induction m using N.peano_rect.
  + intros x n H.
    rewrite N.sub_0_r.
    exact H.
  + intros x n H.
    remember (N.shiftr x m) as x'.
    assert (H':  N.shiftr x m < 2 ^ (n - m)). {
      apply IHm.
      exact H.
    }
    rewrite <- Heqx' in H'.
    rewrite N.sub_succ_r.
    remember (n - m) as r.
    rewrite N.shiftr_succ_r.
    apply div2_prop.
    rewrite <- Heqx'.
    exact H'.
Qed.

Lemma shiftl_shiftr_div
      (x n:  N)
  : N.shiftl (N.shiftr x n) n = (2 ^ n) * (x / (2 ^ n)).
Proof.
  rewrite N.shiftr_div_pow2.
  rewrite N.shiftl_mul_pow2.
  apply N.mul_comm.
Qed.

Lemma shiftr_shiftl_le
      (x n:  N)
  : N.shiftl (N.shiftr x n) n <= x.
Proof.
  rewrite shiftl_shiftr_div.
  remember (2 ^ n) as r.
  apply N.mul_div_le.
  induction n using N.peano_rect.
  + rewrite Heqr.
    intro F.
    discriminate F.
  + rewrite Heqr.
    apply N.neq_0_lt_0.
    apply pow_pos.
    repeat constructor.
Qed.

Lemma split_merge_eq
      (n: N)
      (x: mem (2 * n))
  : mem_eq x (join n (upper_half n x) (lower_half n x)).
Proof.
  constructor.
  destruct x as [x Hx].
  unfold join, lower_half, upper_half, shiftl, shiftr, add, cast, box, unbox.
  unfold mem_val.
  rewrite (N.mod_small (x mod 2 ^ n) (2 ^ (2 * n))).
  + rewrite (N.mod_small ((N.shiftr x n mod 2 ^ (2 * n)) mod 2 ^ n) (2 ^ (2 * n))).
    ++ rewrite (N.mod_small (N.shiftr x n) (2 ^ (2 * n))).
       +++ rewrite (N.mod_small (N.shiftr x n) (2 ^ n)).
           ++++ rewrite (N.mod_small (N.shiftl (N.shiftr x n) n) (2 ^ (2 * n))); [| apply (N.le_lt_trans _ x); [| exact Hx ];
                                                                                    apply shiftr_shiftl_le
                                                                                 ].
                rewrite shiftl_shiftr_div.
                rewrite N.add_comm.
                rewrite <- N.div_mod.
                rewrite (N.mod_small _ _ Hx).
                reflexivity.
                apply N.neq_0_lt_0.
                apply pow_pos.
                repeat constructor.
           ++++ assert (Hhelper:  forall (a:  N), 2 * a - a = a). {
                  clear Hx x n.
                  induction a using N.peano_rect.
                  + reflexivity.
                  + rewrite <- N.double_spec.
                    rewrite <- N.add_1_r.
                    rewrite N.double_add.
                    cbn.
                    rewrite N.double_spec.
                    rewrite (N.add_comm a 1) at 1.
                    rewrite N.sub_add_distr.
                    rewrite <- N.add_sub_assoc.
                    ++ assert (Heq:  2 - 1 = 1). {
                         reflexivity.
                       }
                       rewrite Heq.
                       rewrite (N.add_comm (2*a) 1).
                       rewrite <- N.add_sub_assoc.
                       rewrite IHa.
                       rewrite N.add_comm.
                       reflexivity.
                       clear IHa Heq.
                       induction a using N.peano_rect.
                       reflexivity.
                       rewrite <- N.add_1_r.
                       rewrite N.mul_add_distr_l.
                       apply N.add_le_mono; [ exact IHa |].
                       cbn.
                       apply N.le_succ_diag_r.
                    ++ apply N.le_succ_diag_r.
                }
                rewrite <- (Hhelper n) at 2.
                apply shiftr_reduces'.
                exact Hx.
       +++ apply (N.le_lt_trans _ x); [| exact Hx ].
           apply shiftr_reduces.
    ++ apply (N.lt_le_trans _ (2 ^ n)).
       +++ apply N.mod_bound_pos.
           apply N.le_0_l.
           apply pow_pos.
           apply N.lt_0_2.
       +++ apply N.pow_le_mono_r.
           intro F; discriminate F.
           clear Hx x.
           induction n using N.peano_rect.
           reflexivity.
           rewrite <- N.add_1_r.
           rewrite N.mul_add_distr_l.
           apply N.add_le_mono; [ exact IHn |].
           cbn.
           apply N.le_succ_diag_r.
  + apply (N.lt_le_trans (x mod (2 ^ n)) (2 ^ n)).
    ++ apply N.mod_bound_pos.
       apply N.le_0_l.
       apply pow_pos.
       apply N.lt_0_2.
    ++ apply N.pow_le_mono_r.
       intro F; discriminate F.
       clear Hx x.
       induction n using N.peano_rect.
       reflexivity.
       rewrite <- N.add_1_r.
       rewrite N.mul_add_distr_l.
       apply N.add_le_mono; [ exact IHn |].
       cbn.
       apply N.le_succ_diag_r.
Qed.

Definition upper_word_half
           (x:  word)
  : byte :=
  upper_half 8 x.

Add Parametric Morphism
  : upper_word_half with signature (@mem_eq 16) ==> (@mem_eq 8)
      as upper_word_morphism.
Proof.
  intros x y Heq.
  unfold upper_word_half.
  rewrite Heq.
  reflexivity.
Qed.

Definition lower_word_half
           (x:  word)
  : byte :=
  lower_half 8 x.

Add Parametric Morphism
  : lower_word_half with signature (@mem_eq 16) ==> (@mem_eq 8)
      as lower_word_morphism.
Proof.
  intros x y Heq.
  unfold lower_word_half.
  rewrite Heq.
  reflexivity.
Qed.

Definition join_bytes_to_word
           (b b':  byte)
  : word :=
  join 8 b b'.

Add Parametric Morphism
  : join_bytes_to_word with signature (@mem_eq 8) ==> (@mem_eq 8) ==> (@mem_eq 16)
      as join_bytes_to_word_morphism.
Proof.
  intros x y Heq x' y' Heq'.
  unfold join_bytes_to_word.
  rewrite Heq.
  rewrite Heq'.
  reflexivity.
Qed.

Lemma join_bytes_upper_lower_eq
      (x:  word)
  : mem_eq x (join_bytes_to_word (upper_word_half x) (lower_word_half x)).
Proof.
  unfold join_bytes_to_word, upper_word_half, lower_word_half.
  apply (split_merge_eq 8 x).
Qed.

Definition upper_lword_half
           (l:  lword)
  : word :=
  upper_half 16 l.

Add Parametric Morphism
  : upper_lword_half with signature (@mem_eq 32) ==> (@mem_eq 16)
      as upper_lword_morphism.
Proof.
  intros x y Heq.
  unfold upper_lword_half.
  rewrite Heq.
  reflexivity.
Qed.

Definition lower_lword_half
           (l:  lword)
  : word :=
  lower_half 16 l.

Add Parametric Morphism
  : lower_lword_half with signature (@mem_eq 32) ==> (@mem_eq 16)
      as lower_lword_morphism.
Proof.
  intros x y Heq.
  unfold lower_lword_half.
  rewrite Heq.
  reflexivity.
Qed.

Definition join_words_to_lword
           (w w':  word)
  : lword :=
  join 16 w w'.

Add Parametric Morphism
  : join_words_to_lword with signature (@mem_eq 16) ==> (@mem_eq 16) ==> (@mem_eq 32)
      as join_words_to_word_morphism.
Proof.
  intros x y Heq x' y' Heq'.
  unfold join_bytes_to_word.
  rewrite Heq.
  rewrite Heq'.
  reflexivity.
Qed.

Lemma join_word_upper_lower_eq
      (x:  lword)
  : mem_eq x (join_words_to_lword (upper_lword_half x) (lower_lword_half x)).
Proof.
  unfold join_words_to_lword, upper_word_half, lower_word_half.
  apply (split_merge_eq 16 x).
Qed.

Definition lword_quarter_4
           (l:  lword)
  : byte :=
  upper_word_half (upper_lword_half l).

Add Parametric Morphism
  : lword_quarter_4 with signature (@mem_eq 32) ==> (@mem_eq 8)
      as lword_quarter_4_morphism.
Proof.
  intros x y Heq.
  unfold lword_quarter_4.
  rewrite Heq.
  reflexivity.
Qed.

Definition lword_quarter_3
           (l:  lword)
  : byte :=
  lower_word_half (upper_lword_half l).

Add Parametric Morphism
  : lword_quarter_3 with signature (@mem_eq 32) ==> (@mem_eq 8)
      as lword_quarter_3_morphism.
Proof.
  intros x y Heq.
  unfold lword_quarter_3.
  rewrite Heq.
  reflexivity.
Qed.

Definition lword_quarter_2
           (l:  lword)
  : byte :=
  upper_word_half (lower_lword_half l).

Add Parametric Morphism
  : lword_quarter_2 with signature (@mem_eq 32) ==> (@mem_eq 8)
      as lword_quarter_2_morphism.
Proof.
  intros x y Heq.
  unfold lword_quarter_2.
  rewrite Heq.
  reflexivity.
Qed.

Definition lword_quarter_1
           (l:  lword)
  : byte :=
  lower_word_half (lower_lword_half l).

Add Parametric Morphism
  : lword_quarter_1 with signature (@mem_eq 32) ==> (@mem_eq 8)
      as lword_quarter_1_morphism.
Proof.
  intros x y Heq.
  unfold lword_quarter_1.
  rewrite Heq.
  reflexivity.
Qed.

Definition join_bytes_to_lword
           (b4 b3 b2 b1:  byte)
  : lword :=
  join_words_to_lword (join_bytes_to_word b4 b3) (join_bytes_to_word b2 b1).

Add Parametric Morphism
  : join_bytes_to_lword with signature (@mem_eq 8) ==> (@mem_eq 8) ==> (@mem_eq 8) ==> (@mem_eq 8) ==> (@mem_eq 32)
      as join_bytes_to_lword_morphism.
Proof.
  intros b4 b4' Heq4
         b3 b3' Heq3
         b2 b2' Heq2
         b1 b1' Heq1.
  unfold join_bytes_to_lword.
  rewrite Heq1; rewrite Heq2; rewrite Heq3; rewrite Heq4.
  reflexivity.
Qed.

Lemma join_bytes_lword_eq
      (x:  lword)
  : mem_eq x (join_bytes_to_lword (lword_quarter_4 x)
                                  (lword_quarter_3 x)
                                  (lword_quarter_2 x)
                                  (lword_quarter_1 x)).
Proof.
  unfold join_bytes_to_lword, lword_quarter_4, lword_quarter_3, lword_quarter_2, lword_quarter_1.
  repeat rewrite <- join_bytes_upper_lower_eq.
  rewrite <- join_word_upper_lower_eq.
  reflexivity.
Qed.

(** * Coercion

 *)

Definition make_byte: N -> byte := box 8.
Definition make_word: N -> word := box 16.
Definition make_lword: N -> lword := box 32.

Coercion make_byte:   N >-> byte.
Coercion make_word:   N >-> word.
Coercion make_lword:  N >-> lword.
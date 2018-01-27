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

Class PropBool1
      {A:         Type}
      (pred:      A -> Prop)
      (pred_bool: A -> bool) :=
  { pred_bool_pred_1 (a: A): pred_bool a = true <-> pred a
  }.

Lemma pred_bool_false_1
      {A:         Type}
      (pred:      A -> Prop)
      (pred_bool: A -> bool)
     `{PropBool1 A pred pred_bool}
      (a:         A)
  : pred_bool a = false <-> ~pred a.
Proof.
  split.
  + intros Hpred_bool Hpred.
    apply (pred_bool_pred_1 a) in Hpred.
    rewrite Hpred in Hpred_bool.
    discriminate.
  + intros Hnpred.
    case_eq (pred_bool a); intro Heq.
    ++ apply (pred_bool_pred_1 a) in Heq.
       apply Hnpred in Heq.
       destruct Heq.
    ++ reflexivity.
Qed.

Class PropBool2
      {A:         Type}
      {B:         Type}
      (pred:      A -> B -> Prop)
      (pred_bool: A -> B -> bool) :=
  { pred_bool_pred_2 (a: A)
                     (b: B)
    : pred_bool a b = true <-> pred a b
  }.

Lemma pred_bool_false_2
      {A:         Type}
      {B:         Type}
      (pred:      A -> B -> Prop)
      (pred_bool: A -> B -> bool)
     `{PropBool2 A B pred pred_bool}
      (a:         A)
      (b:         B)
  : pred_bool a b = false <-> ~pred a b.
Proof.
  split.
  + intros Hpred_bool Hpred.
    apply (pred_bool_pred_2 a b) in Hpred.
    rewrite Hpred in Hpred_bool.
    discriminate.
  + intros Hnpred.
    case_eq (pred_bool a b); intro Heq.
    ++ apply (pred_bool_pred_2 a b) in Heq.
       apply Hnpred in Heq.
       destruct Heq.
    ++ reflexivity.
Qed.

Class PropBool3
      {A:         Type}
      {B:         Type}
      {C:         Type}
      (pred:      A -> B -> C -> Prop)
      (pred_bool: A -> B -> C -> bool) :=
  { pred_bool_pred_3 (a: A)
                     (b: B)
                     (c: C)
    : pred_bool a b c = true <-> pred a b c
  }.

Lemma pred_bool_false_3
      {A:         Type}
      {B:         Type}
      {C:         Type}
      (pred:      A -> B -> C -> Prop)
      (pred_bool: A -> B -> C -> bool)
     `{PropBool3 A B C pred pred_bool}
      (a:         A)
      (b:         B)
      (c:         C)
  : pred_bool a b c = false <-> ~pred a b c.
Proof.
  split.
  + intros Hpred_bool Hpred.
    apply (pred_bool_pred_3 a b c) in Hpred.
    rewrite Hpred in Hpred_bool.
    discriminate.
  + intros Hnpred.
    case_eq (pred_bool a b c); intro Heq.
    ++ apply (pred_bool_pred_3 a b c) in Heq.
       apply Hnpred in Heq.
       destruct Heq.
    ++ reflexivity.
Qed.
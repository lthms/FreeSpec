Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import FreeSpec.Control.Either.
Require Import Coq.Program.Equality.

Import ListNotations.
Local Open Scope list_scope.

(* Set Universe Polymorphism. *)

Inductive inhabited : Type.

Polymorphic Fixpoint get
            (set:  list Type)
            (n:    nat)
            {struct n}
  : Type :=
  match n, set with
  | 0, t :: _
    => t
  | S n, _ :: set'
    => get set' n
  | _, _
    => inhabited
  end.

Polymorphic Inductive union
            (set:  list Type)
  : Type :=
| OneOf {t:  Type}
        (n:  nat)
        (H:  get set n = t)
        (x:  t)
  : union set.

Arguments OneOf [set t] (n H x).

Polymorphic Inductive product
  : list Type -> Type :=
| Acons (a:    Type)
        (x:    a)
        (set:  list Type)
        (rst:  product set)
  : product (a :: set)
| Anil
  : product [].

Arguments Acons [a] (x) [set] (rst).

Polymorphic Fixpoint fetch
            {set:  list Type}
            (x:    product set)
            (n:    nat)
  : option (get set n) :=
  match x, n with
  | Acons x _, 0
    => Some x
  | Acons _ rst, S n
    => fetch rst n
  | _, _
    => None
  end.

Polymorphic Class Contains
            (t:    Type)
            (set:  list Type)
  := { rank:            nat
     ; rank_get_t:      get set rank = t
     ; small_set:       list Type
     ; small_set_lt_p:  forall (m:  nat),
         m < rank
         -> get small_set m = get set m
     ; small_set_gt_p:  forall (m:  nat),
         rank <= m
         -> get small_set m = get set (S m)
     ; get_v:           product set -> t
     ; set_v:           t -> product set -> product set
     ; get_set_p:       forall (v:  t)
                               (x:  product set),
         get_v (set_v v x) = v
     ; get_set_np:      forall (v:  t)
                               (x:  product set)
                               (n:  nat),
         n <> rank
         -> fetch x n = fetch (set_v v x) n
     }.

Arguments rank (t set) [_].
Arguments small_set (t set) [_].
Arguments rank_get_t (t set) [_].
Arguments small_set_lt_p (t set) [_] (m _).
Arguments small_set_gt_p (t set) [_] (m _).

Polymorphic Instance Contains_head
            (t:    Type)
            (set:  list Type)
  : Contains t (cons t set) :=
  { rank       := 0
  ; small_set  := set
  }.
+ reflexivity.
+ intros m H.
  apply PeanoNat.Nat.nlt_0_r in H.
  destruct H.
+ intros m H.
  reflexivity.
+ intros x.
  dependent induction x.
  exact x.
+ intros v x.
  apply Acons.
  ++ exact v.
  ++ dependent induction x.
     exact x0.
+ reflexivity.
+ intros v x n H.
  dependent induction n; [ omega |].
  clear IHn.
  dependent induction x.
  clear IHx.
  reflexivity.
Defined.

Polymorphic Instance Contains_tail
            (t any:  Type)
            (set:    list Type)
            (H:      Contains t set)
  : Contains t (cons any set) :=
  { small_set  := any :: small_set t set
  ; rank       := S (rank t set)
  }.
+ cbn.
  apply rank_get_t.
+ intros m Hlt.
  induction m.
  ++ reflexivity.
  ++ clear IHm.
     cbn.
     apply small_set_lt_p.
     apply Lt.lt_S_n in Hlt.
     exact Hlt.
+ intros m Hgt.
  induction m.
  ++ apply PeanoNat.Nat.nlt_0_r in Hgt.
     destruct Hgt.
  ++ clear IHm.
     apply Le.le_S_n in Hgt.
     apply small_set_gt_p in Hgt.
     assert (R: get (any :: small_set t set) (S m) = get (small_set t set) m)
       by reflexivity.
     rewrite R.
     rewrite Hgt.
     reflexivity.
+ intros x.
  dependent induction x.
  exact (get_v x0).
+ intros v x.
  dependent induction x.
  exact (Acons x (set_v v x0)).
+ intros v x.
  dependent induction x.
  apply get_set_p.
+ intros v x n H'.
  dependent induction x.
  clear IHx.
  induction n.
  ++ reflexivity.
  ++ clear IHn.
     cbn.
     apply get_set_np.
     omega.
Defined.

Polymorphic Definition inj
            {t:    Type}
            {set:  list Type} `{Contains t set}
            (x:    t)
  : union set :=
  OneOf (rank t set) (rank_get_t t set) x.

Polymorphic Definition remove
           {set:  list Type}
           (x:    union set)
           (t:    Type) `{Contains t set}
  : Either t (union (small_set t set)).
  refine (
  match x with
  | OneOf n H x
    => _
  end
    ).
  + case_eq (n =? (rank t set));
      intro Heq.
    ++ apply PeanoNat.Nat.eqb_eq in Heq.
       assert (Ht: T = t). {
         rewrite <- H.
         rewrite Heq.
         apply rank_get_t.
       }
       refine (left (eq_rect T id x t Ht)).
    ++ refine (right _).
       case_eq (n <? rank t set).
       +++ intros Hlt.
           apply Nat.ltb_lt in Hlt.
           refine (OneOf n _ x).
           rewrite <- H.
           apply small_set_lt_p.
           apply Hlt.
       +++ intros Hgt.
           apply Nat.ltb_ge in Hgt.
           apply Nat.eqb_neq in Heq.
           assert (Hr: rank t set < n) by omega.
           induction n; [ omega |].
           clear IHn.
           refine (OneOf n _ x).
           rewrite <- H.
           apply small_set_gt_p.
           apply lt_n_Sm_le in Hr.
           exact Hr.
Defined.

Ltac evaluate_exact v :=
  let x := fresh "x" in
  let Heqx := fresh "Heqx" in
  remember v as x eqn:Heqx;
  vm_compute in Heqx;
  match type of Heqx with
  | x = ?ev => exact ev
  end.

Ltac inj v :=
  match goal with
  | [ |- union ?set]
    => evaluate_exact (@inj _ set _ v)
  end.

Section DoesItWork.
  Definition test_bool
    : union [bool; nat] :=
    inj true.

  Definition test_nat
    : union [bool; nat] :=
    inj 0.
End DoesItWork.

Fixpoint visit
         {t:    Type}
         {set:  list Type} `{Contains t set}
         {a:    Type}
         (x:    product set)
         (f:    t -> t * a)
  : product set * a :=
  (set_v (fst (f (get_v x))) x, snd (f (get_v x))).
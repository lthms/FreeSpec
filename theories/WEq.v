Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.PeanoNat.

Require Import FreeSpec.PropBool.

(** * Weaker Equality

    For a number of type, the Coq equality is too strong. Therefore,
    we introduce the idea of a _weaker equality_ one can use in place
    of the Leibniz equality used in Coq.

 *)

Class WEq
      (A: Type) :=
  { weq (a a': A): Prop
  ; rel:> Equivalence weq
  }.

Arguments weq [A _] (_ _).

Infix "==" :=
  weq
    (at level 70, no associativity)
  : free_weq_scope.

Notation "a /= b" :=
  (~ weq a b)
    (at level 70, no associativity)
  : free_weq_scope.

Lemma not_weq_sym
      {A:    Type}
     `{WEq A}
      (x y:  A)
  : ~ weq x y -> ~weq y x.
Proof.
  intros Hneq Heq.
  symmetry in Heq.
  apply Hneq in Heq.
  exact Heq.
Qed.

Local Open Scope free_weq_scope.

(** * Weaker Decidable Equality

    Sometimes, it is not enough to have an equality. Thus, we
    introduce the notion of weaker decidable equality. It comes in two
    “flavors”: one based on sumbool and one based on bool.

 *)

Class WEqDec
      (A: Type)
     `{WEq A} :=
  { weq_dec (a a': A): {weq a a'} + {~weq a a'}
  }.

Arguments weq_dec [A _ _] (_ _).

Infix "=?" :=
  weq_dec
    (at level 70, no associativity)
  : free_weq_scope.

Class WEqBool
      (A: Type)
     `{WEq A} :=
  { weq_bool (a a': A): bool
  ; weq_bool_is_bool_prop :> PropBool2 (@weq A _) weq_bool
  }.

Arguments weq_bool [A _ _] (_ _).

Lemma weq_bool_weq
      {A:    Type}
     `{WEqBool A}
      (a a': A)
  : weq_bool a a' = true <-> weq a a'.
Proof.
  apply pred_bool_pred_2.
Qed.

Lemma weq_bool_refl
      {A: Type}
     `{WEqBool A}
      (a: A)
  : weq_bool a a = true.
Proof.
  apply weq_bool_weq.
  reflexivity.
Qed.

Lemma weq_bool_false
      {A:    Type}
     `{WEqBool A}
      (a a': A)
  : weq_bool a a' = false <-> ~weq a a'.
Proof.
  split.
  + intros Hweq_bool Hweq.
    apply (weq_bool_weq a a') in Hweq.
    rewrite Hweq in Hweq_bool.
    discriminate.
  + intros Hnweq.
    case_eq (weq_bool a a'); intro Heq.
    ++ apply weq_bool_weq in Heq.
       apply Hnweq in Heq.
       destruct Heq.
    ++ reflexivity.
Qed.

Lemma weq_bool_false_rewrite
      {A:    Type}
     `{WEqBool A}
      (x y:  A)
  : ~ weq x y -> weq_bool x y = false.
Proof.
  apply weq_bool_false.
Qed.

Infix "?=" :=
  weq_bool
    (at level 70, no associativity)
  : free_weq_scope.

(** * Instances

    ** Function Instances

 *)

Definition function_weq
           {a b: Type}
          `{WEq b}
           (f g: a -> b)
  : Prop :=
  forall (x: a), f x == g x.

Lemma function_weq_refl
      {a b: Type}
     `{WEq b}
      (f: a -> b)
  : function_weq f f.
Proof.
  intro x.
  reflexivity.
Qed.

Lemma function_weq_sym
      {a b: Type}
     `{WEq b}
      (f g: a -> b)
  : function_weq f g
    -> function_weq g f.
Proof.
  unfold function_weq.
  intros H' x.
  rewrite H'.
  reflexivity.
Qed.

Lemma function_weq_trans
      {a b: Type}
     `{WEq b}
      (f g h: a -> b)
  : function_weq f g
    -> function_weq g h
    -> function_weq f h.
Proof.
  unfold function_weq.
  intros F G x.
  rewrite <- (G x).
  exact (F x).
Qed.

Add Parametric Relation
    (a b: Type)
   `{WEq b}
  : (a -> b) (function_weq)
    reflexivity  proved by function_weq_refl
    symmetry     proved by function_weq_sym
    transitivity proved by function_weq_trans
      as function_web_equiv.

Instance function_WEq
         (a b: Type)
        `{WEq b}
  : WEq (a -> b) :=
  { weq := function_weq
  }.

(** ** Tuple Instances

 *)

Definition tuple_weq
           {a b: Type}
          `{WEq a}
          `{WEq b}
           (o o': a * b)
  : Prop :=
  fst o == fst o' /\ snd o == snd o'.

Lemma tuple_weq_refl
      {a b: Type}
     `{WEq a}
     `{WEq b}
      (o: a * b)
  : tuple_weq o o.
Proof.
  split; reflexivity.
Qed.

Lemma tuple_weq_sym
      {a b: Type}
     `{WEq a}
     `{WEq b}
      (o o': a * b)
  : tuple_weq o o'
    -> tuple_weq o' o.
Proof.
  intros [Hf Hs].
  split; [ rewrite Hf; reflexivity
         | rewrite Hs; reflexivity
         ].
Qed.

Lemma tuple_weq_trans
      {a b: Type}
     `{WEq a}
     `{WEq b}
      (o o' o'': a * b)
  : tuple_weq o o'
    -> tuple_weq o' o''
    -> tuple_weq o o''.
Proof.
  intros [Of Os] [Of' Os'].
  split; [ rewrite Of; exact Of'
         | rewrite Os; exact Os'
         ].
Qed.

Add Parametric Relation
    (a b: Type)
   `{WEq a}
   `{WEq b}
  : (a * b) (tuple_weq)
    reflexivity  proved by tuple_weq_refl
    symmetry     proved by tuple_weq_sym
    transitivity proved by tuple_weq_trans
      as tuple_weq_equiv.

Instance tuple_WEq
         (a b: Type)
        `{WEq a}
        `{WEq b}
  : WEq (a * b) :=
  { weq := tuple_weq
  }.

Add Parametric Morphism
    (a b: Type)
   `{WEq a}
   `{WEq b}
  : fst
    with signature (@weq (a * b) _) ==> (@weq a _)
      as fst_tuple_weq_morphism.
Proof.
  intros o o' [P Q].
  exact P.
Qed.

Add Parametric Morphism
    (a b: Type)
   `{WEq a}
   `{WEq b}
  : snd
    with signature (@weq (a * b) _) ==> (@weq b _)
      as snd_tuple_weq_morphism.
Proof.
  intros o o' [P Q].
  exact Q.
Qed.

Add Parametric Morphism
    (a b: Type)
   `{WEq a}
   `{WEq b}
  : pair
    with signature (@weq a _) ==> (@weq b _) ==> (@weq (a * b) _)
      as pair_tuple_weq_morphism.
Proof.
  intros o o' Heq p p' Heq'.
  constructor; [ exact Heq
               | exact Heq'
               ].
Qed.

Definition tuple_weq_bool
           {a b:  Type}
          `{WEqBool a}
          `{WEqBool b}
           (x y:  a * b)
  : bool :=
  (fst x ?= fst y) && (snd x ?= snd y).

Instance tuple_PropBool
         (a b:  Type)
        `(WEqBool a)
        `(WEqBool b)
  : PropBool2 (@tuple_weq a b _ _) (@tuple_weq_bool a b _ _ _ _) :=
  {
  }.
+ intros x y.
  unfold tuple_weq_bool.
  unfold tuple_weq.
  split.
  ++ intros Hbool.
     apply andb_prop in Hbool.
     destruct Hbool as [Hb Hb'].
     apply pred_bool_pred_2 in Hb.
     apply pred_bool_pred_2 in Hb'.
     split; [ exact Hb | exact Hb' ].
  ++ intros [Hp Hp'].
     apply pred_bool_pred_2 in Hp.
     apply pred_bool_pred_2 in Hp'.
     apply andb_true_intro.
     split; [ exact Hp | exact Hp' ].
Defined.

(** ** Nat

 *)

Instance nat_WEq
  : WEq nat :=
  { weq := eq
  }.

Instance nat_eq_eqb_PropBool2
  : PropBool2 (@eq nat) (Nat.eqb) :=
  {
  }.
+ apply Nat.eqb_eq.
Defined.

Instance nat_WEqBool
  : WEqBool nat :=
  { weq_bool := Nat.eqb
  }.

(** * Bool

 *)

Instance bool_WEq
  : WEq bool :=
  { weq := eq
  }.

Instance bool_eq_eqb_PropBool2
  : PropBool2 (@eq bool) (Bool.eqb) :=
  {
  }.
+ apply Bool.eqb_true_iff.
Defined.

Instance bool_WEqBool
  : WEqBool bool :=
  { weq_bool := Bool.eqb
  }.

(** * Option

 *)

Inductive option_weq
          {a:    Type}
         `{WEq a}
  : option a -> option a -> Prop :=
| option_weq_some (x:    a)
                  (y:    a)
                  (Heq:  x == y)
  : option_weq (Some x) (Some y)
| option_weq_none
  : option_weq None None.

Lemma option_weq_refl
      {a:  Type}
     `{WEq a}
      (x:  option a)
  : option_weq x x.
Proof.
  destruct x; constructor.
  reflexivity.
Qed.

Lemma option_weq_sym
      {a:    Type}
     `{WEq a}
      (x y:  option a)
  : option_weq x y
    -> option_weq y x.
Proof.
  intro Heq.
  destruct x; inversion Heq; constructor.
  symmetry; exact Heq0.
Qed.

Lemma option_weq_trans
      {a:      Type}
     `{WEq a}
      (x y z:  option a)
  : option_weq x y
    -> option_weq y z
    -> option_weq x z.
Proof.
  intros Heq Heq'.
  induction Heq'.
  + induction x.
    ++ constructor.
       inversion Heq.
       rewrite <- Heq0.
       exact Heq1.
    ++ inversion Heq.
  + inversion Heq.
    constructor.
Qed.

Add Parametric Relation
    (a:  Type)
   `{WEq a}
  : (option a) (option_weq)
    reflexivity proved by   option_weq_refl
    symmetry proved by      option_weq_sym
    transitivity proved by  option_weq_trans
      as option_weq_relation.

Instance option_WEq
         (a:  Type)
        `{WEq a}
  : WEq (option a) :=
  { weq := option_weq
  }.

Add Parametric Morphism
    (a:  Type)
   `{WEq a}
  : (@Some a)
    with signature (@weq a _) ==> (@weq (option a) _)
      as some_weq_morphism.
  + intros x y Heq.
    constructor.
    exact Heq.
Qed.

Definition option_weq_bool
           {a:    Type}
          `{WEqBool a}
           (x y:  option a)
  : bool :=
  match x, y with
  | Some x, Some y
    => x ?= y
  | None, None
    => true
  | _, _
    => false
  end.

Instance option_weq_bool_prop
         (a:  Type)
        `{WEqBool a}
  : PropBool2 (@weq (option a) _) (@option_weq_bool a _ _) :=
  {
  }.
+ intros x y.
  split; [ intro Hb | intro Hp ].
  ++ destruct x; induction y; try discriminate.
     +++ constructor.
         apply pred_bool_pred_2.
         exact Hb.
     +++ constructor.
  ++ induction Hp.
     +++ cbn.
         apply pred_bool_pred_2.
         exact Heq.
     +++ reflexivity.
Defined.

Instance option_WEqBool
         (a:  Type)
        `{WEqBool a}
  : WEqBool (option a) :=
  { weq_bool := option_weq_bool
  }.

(** * List

 *)

Inductive list_weq
          {a:  Type}
         `{WEq a}
  : list a -> list a -> Prop :=
| list_weq_cons (x y:   a)
                (r r':  list a)
                (Heq:   x == y)
                (Heq':  list_weq r r')
  : list_weq (cons x r) (cons y r')
| list_weq_nil
  : list_weq nil nil.

Lemma list_weq_refl
      {a:  Type}
     `{WEq a}
      (l:  list a)
  : list_weq l l.
Proof.
  induction l.
  + constructor.
  + constructor; [ reflexivity
                 | exact IHl
                 ].
Qed.

Lemma list_weq_sym
      {a:     Type}
     `{WEq a}
      (l l':  list a)
  : list_weq l l'
    -> list_weq l' l.
Proof.
  intros Heq; induction Heq.
  + constructor.
    ++ symmetry; exact Heq.
    ++ exact IHHeq.
  + constructor.
Qed.

Lemma list_weq_trans
      {a:     Type}
     `{WEq a}
      (l l' l'':  list a)
  : list_weq l l'
    -> list_weq l' l''
    -> list_weq l l''.
Proof.
  revert l' l''.
  induction l; intros l' l''.
  + intros Heq Heq'.
    inversion Heq; subst.
    inversion Heq'; subst.
    constructor.
  + intros Heq Heq'.
    inversion Heq; subst.
    inversion Heq'; subst.
    constructor.
    ++ rewrite Heq0.
       exact Heq1.
    ++ apply (IHl r' r'0 Heq'0 Heq'1).
Qed.

Add Parametric Relation
    (a:  Type)
   `{WEq a}
  : (list a) (list_weq)
    reflexivity  proved by list_weq_refl
    symmetry     proved by list_weq_sym
    transitivity proved by list_weq_trans
      as list_web_equiv.

Instance list_WEq
         (a:  Type)
        `{WEq a}
  : WEq (list a) :=
  { weq := list_weq
  }.

Fixpoint list_weq_bool
         {a:     Type}
        `{WEqBool a}
         (l l':  list a)
  : bool :=
  match l, l' with
  | cons x r, cons x' r'
    => (x ?= x') && (list_weq_bool r r')
  | nil, nil
    => true
  | _, _
    => false
  end.

Instance list_weq_propbool
         (a:  Type)
        `{WEqBool a}
  : PropBool2 (@weq (list a) _) list_weq_bool :=
  {
  }.
+ induction a0; induction b.
  ++ split; reflexivity.
  ++ split; [ discriminate |].
     intros Hf; inversion Hf.
  ++ split; [ discriminate |].
     intros Hf; inversion Hf.
  ++ split.
     +++ intros Hweq.
         apply Bool.andb_true_iff in Hweq.
         fold list_weq_bool in Hweq.
         destruct Hweq as [H1 H2].
         constructor.
         ++++ apply pred_bool_pred_2.
              exact H1.
         ++++ apply IHa0 in H2.
              exact H2.
     +++ intros Heq.
         inversion Heq; subst.
         apply Bool.andb_true_iff.
         fold list_weq_bool.
         apply pred_bool_pred_2 in Heq0.
         split; [ exact Heq0 |].
         apply IHa0.
         exact Heq'.
Qed.

Instance list_WEqBool
         (a:  Type)
        `{WEqBool a}
  : WEqBool (list a) :=
  {
  }.

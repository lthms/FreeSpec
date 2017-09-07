Require Import Coq.Setoids.Setoid.

Require Import FreeSpec.Control.
Require Import FreeSpec.WEq.

Local Open Scope free_weq_scope.
Local Open Scope list_scope.

(* WORK IN PROGRESS *)

Fixpoint list_map
         {a b:  Type}
         (f:    a -> b)
         (l:    list a)
  : list b :=
  match l with
  | nil
    => nil
  | x :: r => (f x) :: (list_map f r)
  end.

Lemma list_map_nil
      {a b:  Type}
      (f:    a -> b)
  : list_map f nil = nil.
Proof.
  reflexivity.
Qed.

Instance list_Functor
  : Functor list :=
  { map := @list_map
  }.
+ intros a Ha x.
  induction x; constructor.
  ++ reflexivity.
  ++ exact IHx.
+ intros a b c Hc u v x.
  induction x; constructor.
  ++ reflexivity.
  ++ exact IHx.
Defined.

Definition list_pure
           {a:  Type}
           (x:  a)
  : list a :=
  x :: nil.

Fixpoint concat
         {a:     Type}
         (l l':  list a)
  : list a :=
  match l with
  | nil => l'
  | x :: r => x :: (concat r l')
  end.

Add Parametric Morphism
    (a:  Type)
   `{WEq a}
  : concat
    with signature (@weq (list a) _) ==> (@weq (list a) _) ==> (@weq (list a) _)
      as concat_list_morphism.
Proof.
  induction x.
  + intros y Heq x' y' Heq'.
    inversion Heq; subst.
    exact Heq'.
  + intros y Heq x' y' Heq'.
    inversion Heq; subst.
    cbn.
    constructor.
    ++ exact Heq0.
    ++ apply IHx.
       exact Heq'0.
       exact Heq'.
Qed.

Lemma concat_nil
      {a:  Type}
      (l:  list a)
  : concat l nil = l.
Proof.
  induction l.
  + reflexivity.
  + cbn.
    rewrite IHl.
    reflexivity.
Qed.

Fixpoint list_join
         {a:  Type}
         (l:  list (list a))
  : list a :=
  match l with
  | cons x r
    => concat x (list_join r)
  | nil => nil
  end.

Fixpoint list_app
         {a b:  Type}
         (f:    list (a -> b))
         (l:    list a)
  : list b :=
  match f with
  | f :: r
    => concat (f <$> l) (list_app r l)
  | nil
    => nil
  end.

Lemma list_app_nil
      {a b:  Type}
      (f:    list (a -> b))
  : list_app f nil = nil.
Proof.
  induction f.
  + reflexivity.
  + cbn.
    exact IHf.
Qed.

Instance list_Applicative
  : Applicative list :=
  { pure := @list_pure
  ; apply := @list_app
  }.
+ intros a Ha v.
  induction v.
  ++ reflexivity.
  ++ constructor.
     reflexivity.
     exact IHv.
+ intros a b c Hc u v w.
Admitted.
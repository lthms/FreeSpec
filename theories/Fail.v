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

Require Import Coq.Program.Equality.

Require Import FreeSpec.Control.
Require Import FreeSpec.Specification.
Require Import FreeSpec.Control.Either.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Program.
Require Import FreeSpec.WEq.

Local Open Scope free_control_scope.
Local Open Scope free_weq_scope.

(** * Interface

 *)

Inductive FailInterface
          (Err:  Type)
          (I:    Interface)
  : Interface :=
| effect_may_fail {R:  Type}
                  (e:  I R)
  : FailInterface Err I (Either Err R).

Arguments effect_may_fail [Err I R] (e).

(** * FailProgram Monad

   ** Definition

 *)

Inductive FailProgram
          (Err:  Type)
          (I:    Interface)
  : Type -> Type :=
| program_may_fail {R:  Type}
                   (p:  Program (FailInterface Err I) (Either Err R))
  : FailProgram Err I R.

Arguments program_may_fail [Err I R] (p).

Definition runFailProgram
           {Err:  Type}
           {I:    Interface}
           {A:    Type}
           (p:    FailProgram Err I A)
  : Program (FailInterface Err I) (Either Err A) :=
  match p with program_may_fail p => p end.

(** ** Equality

 *)

Definition failProgram_weq
           {Err:  Type}
           {I:    Interface}
           {A:    Type}
           (p q:  FailProgram Err I A)
  : Prop :=
  runFailProgram p == runFailProgram q.

Lemma failProgram_weq_refl
      {Err:  Type}
      {I:    Interface}
      {A:    Type}
      (p:    FailProgram Err I A)
  : failProgram_weq p p.
Proof.
  induction p.
  cbn; reflexivity.
Qed.

Lemma failProgram_weq_sym
      {Err:  Type}
      {I:    Interface}
      {A:    Type}
      (p q:  FailProgram Err I A)
  : failProgram_weq p q
    -> failProgram_weq q p.
Proof.
  induction p; induction q.
  cbn.
  intros Heq.
  symmetry.
  exact Heq.
Qed.

Lemma failProgram_weq_trans
      {Err:    Type}
      {I:      Interface}
      {A:      Type}
      (p q r:  FailProgram Err I A)
  : failProgram_weq p q
    -> failProgram_weq q r
    -> failProgram_weq p r.
Proof.
  induction p; induction q; induction r.
  cbn.
  intros H1 H2.
  transitivity p0; [ exact H1
                   | exact H2
                   ].
Qed.

Add Parametric Relation
    (Err:  Type)
    (I:    Interface)
    (A:    Type)
  : (FailProgram Err I A) failProgram_weq
    reflexivity proved by failProgram_weq_refl
    symmetry proved by failProgram_weq_sym
    transitivity proved by failProgram_weq_trans
      as fail_program_relation.

Instance FailProgram_WEq
         (Err:  Type)
         (I:    Interface)
         (A:    Type)
  : WEq (FailProgram Err I A) :=
  { weq := failProgram_weq
  }.

Definition fail_program_map
           (Err:  Type) `{WEq Err}
           (I:    Interface)
           (A B:  Type)
           (f:    A -> B)
           (p:    FailProgram Err I A)
  : FailProgram Err I B :=
  program_may_fail (map f <$> runFailProgram p).

(** ** Typeclass Instances

 *)

Instance FailProgram_Functor
         (Err:  Type) `{WEq Err}
         (I:    Interface)
  : Functor (FailProgram Err I) :=
  { map := fail_program_map Err I
  }.
Proof.
  + intros A Ha [p].
    constructor; intro int.
    ++ cbn.
       fold (evalProgram int p0).
       induction (evalProgram int p0); reflexivity.
    ++ reflexivity.
  + intros A B C Hc u v x.
    induction x.
    constructor; intros int.
    ++ cbn.
       fold (evalProgram int p).
       induction (evalProgram int p); reflexivity.
    ++ reflexivity.
Defined.

Definition failProgram_pure
           (Err:  Type) `{WEq Err}
           (I:    Interface)
           (A:    Type)
           (x:    A)
  : FailProgram Err I A :=
  program_may_fail (I:=I) (R:=A) $ pure (pure x:  Either Err A).

Definition failProgram_apply
           (Err:    Type) `{WEq Err}
           (I:      Interface)
           (A B:    Type)
           (pf:     FailProgram Err I (A -> B))
           (px:     FailProgram Err I A)
  : FailProgram Err I B :=
  program_may_fail (fe <- runFailProgram pf                       ;
                    xe <- runFailProgram px                       ;
                    pure (f <- fe                                 ;
                          x <- xe                                 ;
                          pure (f x))).

Instance failProgram_Applicative
         (Err:  Type) `{WEq Err}
         (I:    Interface)
  : Applicative (FailProgram Err I) :=
  { apply := failProgram_apply Err I
  ; pure  := failProgram_pure Err I
  }.
Proof.
  + intros A Ha v.
    induction v.
    constructor; intros int.
    ++ cbn.
       fold (evalProgram int p);
         induction (evalProgram int p);
         reflexivity.
    ++ reflexivity.
  + intros A B C Hc u v w.
    induction w.
    dependent induction u.
    dependent induction v.
    cbn.
    constructor; intros int.
    ++ cbn.
       fold (evalProgram int p).
       fold (execProgram int p).
       fold (evalProgram (execProgram int p) p0).
       fold (execProgram (execProgram int p) p0).
       fold (evalProgram (execProgram (execProgram int p) p0) p1).
       induction (evalProgram int p);
         induction (evalProgram (execProgram int p) p0);
         induction (evalProgram (execProgram (execProgram int p) p0) p1);
         reflexivity.
    ++ reflexivity.
  + intros A B Hb v x.
    constructor; intros int; reflexivity.
  + intros A B Hb u x.
    constructor; intros int; reflexivity.
  + intros A B Hb g x.
    induction x.
    constructor; intros int.
    ++ cbn.
       induction (fst (runProgram int p)); reflexivity.
    ++ reflexivity.
Defined.

Definition failProgram_bind
           (Err:  Type) `{WEq Err}
           (I:    Interface)
           (A B:  Type)
           (p:    FailProgram Err I A)
           (f:    A -> FailProgram Err I B)
  : FailProgram Err I B :=
  program_may_fail (xe <- runFailProgram p     ;
                    match xe with
                    | right x
                      => runFailProgram (f x)
                    | left e
                      => pure (left e)
                    end).

Instance FailProgram_Monad
         (Err:  Type) `{WEq Err}
         (I:    Interface)
  : Monad (FailProgram Err I) :=
  { bind := failProgram_bind Err I
  }.
Proof.
  + intros A B Hb x f.
    constructor; intros int; reflexivity.
  + intros A Ha x.
    induction x.
    constructor; intros int.
    ++ cbn.
       unfold program_bind.
       rewrite eval_program_bind_assoc.
       induction (evalProgram int p); reflexivity.
    ++ cbn.
       unfold program_bind.
       rewrite exec_program_bind_assoc.
       induction (evalProgram int p); reflexivity.
  + intros A B C Hc f g h.
    induction f.
    constructor; intros int.
    ++ cbn.
       unfold program_bind.
       remember (fun (xe:  Either Err R)
                 =>  match xe with
                     | left e => program_pure (left e)
                     | right x => runFailProgram (g x)
                     end) as f1.
       remember (fun (xe:  Either Err B)
                 => match xe with
                    | left e => program_pure (left e)
                    | right x => runFailProgram (h x)
                    end) as f2.
       assert (Bind (Bind p f1) f2 == Bind p (fun x => Bind (f1 x) f2))
         by (constructor; reflexivity).
       rewrite H0.
       rewrite Heqf1.
       rewrite Heqf2.
       repeat rewrite eval_program_bind_assoc.
       induction (evalProgram int p); reflexivity.
    ++ cbn.
       unfold program_bind.
       remember (fun (xe:  Either Err R)
                 =>  match xe with
                     | left e => program_pure (left e)
                     | right x => runFailProgram (g x)
                     end) as f1.
       remember (fun (xe:  Either Err B)
                 => match xe with
                    | left e => program_pure (left e)
                    | right x => runFailProgram (h x)
                    end) as f2.
       assert (Bind (Bind p f1) f2 == Bind p (fun x => Bind (f1 x) f2))
         by (constructor; reflexivity).
       rewrite H0.
       rewrite Heqf1.
       rewrite Heqf2.
       repeat rewrite exec_program_bind_assoc.
       induction (evalProgram int p); reflexivity.
  + intros A B Ha x f f' Heq.
    induction x.
    cbn.
    constructor; intros int.
    ++ unfold program_bind.
       repeat rewrite eval_program_bind_assoc.
       induction (evalProgram int p); try reflexivity.
       assert (Heq2:  runFailProgram (f y) == runFailProgram (f' y)) by apply Heq.
       rewrite Heq2.
       reflexivity.
    ++ unfold program_bind.
       repeat rewrite exec_program_bind_assoc.
       induction (evalProgram int p); try reflexivity.
       assert (Heq2:  runFailProgram (f y) == runFailProgram (f' y)) by apply Heq.
       rewrite Heq2.
       reflexivity.
  + intros A B Hb x f.
    induction x.
    cbn.
    constructor; intros int.
    ++ unfold program_map, program_bind.
       repeat rewrite eval_program_bind_assoc.
       induction (evalProgram int p); reflexivity.
    ++ unfold program_map, program_bind.
       repeat rewrite exec_program_bind_assoc.
       induction (evalProgram int p); reflexivity.
Defined.

(** ** Monadic Operatinos

 *)

Definition throw
           {Err:  Type}
           {I:    Interface}
           {A:    Type}
           (err:  Err)
  : FailProgram Err I A :=
  program_may_fail (I:=I) (R:=A) $ pure (left err).

Definition catch
           {Err:  Type}
           {I:    Interface}
           {A:    Type}
           (p:    FailProgram Err I A)
           (f:    Err -> FailProgram Err I A)
  : FailProgram Err I A :=
  program_may_fail (runFailProgram p >>= fun (x:  Either Err A)
                                         => match x with
                                            | right res
                                              => pure x
                                            | left err
                                              => runFailProgram (f err)
                                            end).

Notation "'try!' p 'catch!' x '=>' q" := (catch p (fun x => q))
                                          (at level 99, no associativity).

Section TEST_NOTATION.
  Variables (Err:  Type)
            (err:  Err)
            (I:    Interface)
            (A:    Type).

  Let dummy_catch
    : FailProgram Err I A :=
    try! throw err
    catch! err
    => throw err.
End TEST_NOTATION.

(** * Specification

 *)

Definition fail_abstract_step
           {Err:  Type}
           {I:    Interface}
           {W:    Type}
           (c:    Specification W I)
           (A:    Type)
           (e:    FailInterface Err I A)
           (x:    A)
           (w:    W) :=
  match e, x with
  | effect_may_fail e, right x
    => abstract_step c e x w
  | _, _
    => w
  end.

Inductive fail_precondition
          {Err:  Type}
          {I:    Interface}
          {W:    Type}
          (c:    Specification W I)
  : forall (A:  Type), FailInterface Err I A -> W -> Prop :=
| fail_req (A:  Type)
           (e:  I A)
           (w:  W)
           (H:  precondition c e w)
  : fail_precondition c (Either Err A) (effect_may_fail e) w.

Inductive fail_postcondition
          {Err:  Type}
          {I:    Interface}
          {W:    Type}
          (c:    Specification W I)
  : forall (A:  Type), FailInterface Err I A -> A -> W -> Prop :=
| fail_right (A:  Type)
             (e:  I A)
             (x:  A)
             (w:  W)
             (H:  postcondition c e x w)
  : fail_postcondition c (Either Err A) (effect_may_fail e) (right x) w
| fail_left (A:    Type)
            (i:    I A)
            (err:  Err)
            (w:    W)
  : fail_postcondition c (Either Err A) (effect_may_fail i) (left err) w.

Definition FailSpecs
           {Err:  Type}
           {I:    Interface}
           {W:    Type}
           (c:    Specification W I)
  : Specification W (FailInterface Err I) :=
  {| abstract_step := fail_abstract_step c
   ; precondition := fail_precondition c
   ; postcondition := fail_postcondition c
   |}.
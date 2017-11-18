Require Import Coq.Program.Equality.

Require Import FreeSpec.Control.
Require Import FreeSpec.Contract.
Require Import FreeSpec.Control.Either.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Interp.
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
| instruction_may_fail {R:  Type}
                       (i:  I R)
  : FailInterface Err I (Either Err R).

Arguments instruction_may_fail [Err I R] (i).

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
       assert (pbind (pbind p f1) f2 == pbind p (fun x => pbind (f1 x) f2))
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
       assert (pbind (pbind p f1) f2 == pbind p (fun x => pbind (f1 x) f2))
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
            (e:    Err)
            (I:    Interface)
            (A:    Type).

  Let dummy_catch
    : FailProgram Err I A :=
    try! throw e
    catch! e
    => throw e.
End TEST_NOTATION.

(** * Contracts

 *)

Definition fail_abstract_step
           {Err:  Type}
           {I:    Interface}
           {W:    Type}
           (c:    Contract W I)
           (A:    Type)
           (i:    FailInterface Err I A)
           (x:    A)
           (w:    W) :=
  match i, x with
  | instruction_may_fail i, right x
    => abstract_step c i x w
  | _, _
    => w
  end.

Definition fail_requirements
           {Err:  Type}
           {I:    Interface}
           {W:    Type}
           (c:    Contract W I)
           (A:    Type)
           (i:    FailInterface Err I A)
           (w:    W)
  : Prop :=
  match i with
  | instruction_may_fail i
    => requirements c i w
  end.

Definition fail_promises
           {Err:  Type}
           {I:    Interface}
           {W:    Type}
           (c:    Contract W I)
           (A:    Type)
           (i:    FailInterface Err I A)
           (x:    A)
           (w:    W)
  : Prop :=
  match i, x with
  | instruction_may_fail i, right x
    => promises c i x w
  | _, _
    => True
  end.

Definition FailContract
           {Err:  Type}
           {I:    Interface}
           {W:    Type}
           (c:    Contract W I)
  : Contract W (FailInterface Err I) :=
  {| abstract_step := fail_abstract_step c
   ; requirements := fail_requirements c
   ; promises := fail_promises c
   |}.
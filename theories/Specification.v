(* begin hide *)
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Logic.Classical.
(* end hide *)

Require Import FreeSpec.Program.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Abstract.

(** * Abstract Specification Definition

    An Abstract Specification allows for defining an expected
    behaviour for an [Interface] operational [Semantics]. This
    behaviour is expressed with two complementary predicates:

    - The [precondition] an [Interface] user has to enforce
    - The [postcondition] a [Semantics] has to enforce in return

    These predicates are tied to an abstract state. This abstract
    state is modified by the [abstract_step] function through the
    execution (see [abstractRun] for more information about that).

 *)

Record Specification
       (W:  Type)
       (I:  Interface)
  :=
    { abstract_step (A:  Type)
                    (e:  I A)
                    (x:  A)
      : W -> W
    ; precondition (A:  Type)
      : I A -> W -> Prop
    ; postcondition (A:  Type)
      : I A -> A -> W -> Prop
    }.

Arguments abstract_step [_ _] (_) [_] (_ _ _).
Arguments precondition  [_ _] (_) [_] (_ _).
Arguments postcondition [_ _] (_) [_] (_ _).

Definition specification_derive
           {W:    Type}
           {I:    Interface}
           {A:    Type}
           (p:    Program I A)
           (sig:  Semantics I)
           (c:    Specification W I)
           (w:    W)
  : W :=
  deriveAbstraction w (abstract_step c) sig p.

Fact specification_derives_pure_eq
     {W:    Type}
     {I:    Interface}
     {A:    Type}
     (x:    A)
     (sig:  Semantics I)
     (c:    Specification W I)
     (w:    W)
  : specification_derive (Pure x) sig c w = w.
Proof.
  reflexivity.
Qed.

Fact specification_derives_specification_step
     {W:    Type}
     {I:    Interface}
     {A:    Type}
     (e:    I A)
     (sig:  Semantics I)
     (c:    Specification W I)
     (w:    W)
  : specification_derive (Request e) sig c w
    = abstract_step c e (evalEffect sig e) w.
Proof.
  reflexivity.
Qed.

(** ** Specification Compliance

    A [Semantics] complies with a given abstract [Specification] [c]
    (i.e. it is a [compliante semantics]) if, for every effect which
    satisfies the [precondition], it computes a result which satisfies
    the [postcondition].

    The abstract Specification is parameterized by an abstract state
    and, by definition, if a [Semantics] complies with a
    [Specification] [c] in accordance with a given abstract state and
    executes an effect which satisfies the precondition, then the
    resulting operational Semantics complies with [c] in accordance
    with the new abstract state computed with the [abstract_step]
    function.

 *)

CoInductive compliant_semantics
            {W:    Type}
            {I:    Interface}
            (c:    Specification W I)
            (w:    W)
            (sig:  Semantics I)
  : Prop :=
| enforced (Hprom: forall {A:  Type}
                          (e:  I A),
               precondition c e w
               -> (postcondition c e) (evalEffect sig e) w)
           (Henf:  forall {A:  Type}
                          (e:  I A),
               precondition c e w
               -> compliant_semantics c
                                      (abstract_step c e (evalEffect sig e) w)
                                      (execEffect sig e))
  : compliant_semantics c w sig.

Notation "sig '|=' c '[' w ']'" :=
  (compliant_semantics c w sig)
    (at level 60, no associativity).

Corollary compliant_enforces_postcondition
      {W:     Type}
      {I:     Interface}
      {A:     Type}
      (e:     I A)
      (sig:   Semantics I)
      (c:     Specification W I)
      (w:     W)
      (Henf:  sig |= c[w])
      (Hreq:  precondition c e w)
  : postcondition c e (evalEffect sig e) w.
Proof.
  destruct Henf.
  apply Hprom.
  exact Hreq.
Qed.

(** ** Compliant Stateful Semantics

 *)

Definition specification_preserves_inv
           {W:      Type}
           {I:      Interface}
           {S:      Type}
           (c:      Specification W I)
           (inv:    W -> S -> Prop)
           (step:   @PS I S)
  := forall (A:  Type)
            (e:  I A)
            (w:  W)
            (s:  S),
    inv w s
    -> precondition c e w
    -> inv (abstract_step c e (fst (step A s e)) w) (snd (step A s e)).

Definition specification_enforces_postcondition
           {W:     Type}
           {I:     Interface}
           {S:     Type}
           (c:     Specification W I)
           (inv:   W -> S -> Prop)
           (step:  @PS I S)
  := forall (A:  Type)
            (e:  I A)
            (s:  S)
            (w:  W),
    inv w s
    -> precondition c e w
    -> postcondition c e (fst (step A s e)) w.

Fact _stateful_specification_enforcement
     {W:     Type}
     {I:     Interface}
     {S:     Type}
     (c:     Specification W I)
     (inv:   W -> S -> Prop)
     (step:  @PS I S)
  : forall (w:      W)
           (Hpres:  specification_preserves_inv c inv step)
           (Henf:   specification_enforces_postcondition c inv step)
           (s:      S),
    inv w s
    -> (mkSemantics step s) |= c[w].
Proof.
  cofix.
  intros w Hpres Henf s Hinv .
  constructor.
  + intros A e Hreq.
    unfold specification_enforces_postcondition in Henf.
    cbn in *.
    apply (Henf A e s w Hinv Hreq).
  + intros A e Hreq.
    apply _stateful_specification_enforcement.
    ++ apply  Hpres.
    ++ apply  Henf.
    ++ cbn in *.
       apply (Hpres _ _ _ _ Hinv Hreq).
Qed.

Lemma stateful_specification_enforcement
      {I:     Interface}
      {W:     Type}
      {S:     Type}
      (c:     Specification W I)
      (w:     W)
      (inv:   W -> S -> Prop)
      (step:  @PS I S)
      (Hpres: specification_preserves_inv c inv step)
      (Henf:  specification_enforces_postcondition c inv step)
  : forall (s: S),
    inv w s
    -> (mkSemantics step s) |= c[w].
Proof.
  intros s Hinv.
  apply (_stateful_specification_enforcement c inv step w Hpres Henf s Hinv).
Qed.

(** * Correct Program

    In a nutshell, a given [p: Program I A] is said correct with
    respect to a given abstract [Specification] [c] if, given a
    semantics for [I] which complies with [c] in accordance with [w:
    W], [p] only uses effects which satisfy the precondition.

    ** Definition

 *)

Inductive correct_program
          {W:  Type}
          {I:  Interface}
          (c:  Specification W I)
          (w:  W)
  : forall {A:  Type}, Program I A -> Prop :=
| compliant_request {A:     Type}
                    (e:     I A)
                    (Hreq:  precondition c e w)
  : correct_program c w (Request e)
| compliant_ret {A:  Type}
                (x:  A)
  : correct_program c w (Pure x)
| compliant_inv {A B:    Type}
                (p:      Program I A)
                (f:      A -> Program I B)
                (Hcp:    correct_program c w p)
                (Hnext:  forall (sig: Semantics I)
                               (Henf: sig |= c[w]),
                    correct_program c
                                    (specification_derive p sig c w)
                                    (f (evalProgram sig p)))
  : correct_program c w (Bind p f).

Notation "p '=|' c '[' w ']'" :=
  (correct_program c w p)
    (at level 59, no associativity).

(** ** Compliance Preservation

    In order to prove the [compliance_correct_compliance] lemmas, we
    first highlight several convenient properties of
    [compliant_semantics] and [correct_program].

 *)

Fact correct_program_bind_pure
     {W:    Type}
     {I:    Interface}
     {A B:  Type}
     (a:    A)
     (f:    A -> Program I B)
     (c:    Specification W I)
     (w:    W)
  : f a =| c[w]
    -> Bind (Pure a) f =| c[w].
Proof.
  intros Hp.
  constructor.
  + constructor.
  + intros sig Henf.
    cbn.
    exact Hp.
Qed.

Fact correct_effect_compliant_semantics
     {W:    Type}
     {I:    Interface}
     {A:    Type}
     (e:    I A)
     (sig:  Semantics I)
     (c:    Specification W I)
     (w:    W)
     (H:    sig |= c[w])
     (Hp:   Request e =| c[w])
  : (abstractExec w (abstract_step c) sig (Request e))
      |= c[specification_derive (Request e) sig c w].
Proof.
  cbn.
  constructor.
  + intros B e' Heff.
    destruct H as [Hprom Henf].
    inversion Hp.
    apply Henf in Hreq.
    apply inj_pair2 in H1.
    subst.
    inversion Hreq.
    apply Hprom0.
    exact Heff.
  + intros B e' Heff.
    destruct H as [Hprom Henf].
    inversion Hp.
    apply Henf in Hreq.
    apply inj_pair2 in H1.
    subst.
    inversion Hreq.
    apply Henf0.
    exact Heff.
Qed.

Fact pure_compliant_semantics
     {W:    Type}
     {I:    Interface}
     {A:    Type}
     (x:    A)
     (sig:  Semantics I)
     (c:    Specification W I)
     (w:    W)
     (H:    sig |= c[w])
  : abstractExec w (abstract_step c) sig (Pure x)
      |= c[specification_derive (Pure x) sig c w].
Proof.
  rewrite (specification_derives_pure_eq x sig c).
  exact H.
Qed.

Fact specification_derive_assoc
     {W:      Type}
     {I:      Interface}
     {A B C:  Type}
     (p:      Program I A)
     (f:      A -> Program I B)
     (g:      B -> Program I C)
     (sig:    Semantics I)
     (c:      Specification W I)
     (w:      W)
  : specification_derive (Bind (Bind p f) g) sig c w
    = specification_derive (Bind p (fun x => Bind (f x) g)) sig c w.
Proof.
  reflexivity.
Qed.

Fact exec_abs_assoc
     {W:  Type}
     {I:  Interface}
     {A:  Type}
     (p:  Program I A)
  : forall {B:    Type}
           (f:    A -> Program I B)
           (sig:  Semantics I)
           (c:    Specification W I)
           (w:    W),
    abstractExec w (abstract_step c) sig (Bind p f)
    = abstractExec (specification_derive p sig c w)
                   (abstract_step c)
                   (abstractExec w (abstract_step c) sig p)
                   (f (evalProgram sig p)).
Proof.
  intros B f sig c s.
  repeat rewrite abstract_exec_exec_program_same.
  reflexivity.
Qed.

Fact eval_program_assoc
     {W:  Type}
     {I:  Interface}
     {A:  Type}
     (p:  Program I A)
  : forall {B:    Type}
           (f:    A -> Program I B)
           (sig:  Semantics I)
           (c:    Specification W I)
           (w:    W),
    evalProgram sig (Bind p f)
    = evalProgram (abstractExec w (abstract_step c) sig p)
                  (f (evalProgram sig p)).
Proof.
  intros B f sig c s.
  rewrite abstract_exec_exec_program_same.
  reflexivity.
Qed.

Fact specification_derive_bind
     {W:  Type}
     {I:  Interface}
     {A:  Type}
     (p:  Program I A)
  : forall {B:    Type}
           (f:    A -> Program I B)
           (sig:  Semantics I)
           (c:    Specification W I)
           (w:    W),
    specification_derive (f (evalProgram sig p))
                         (abstractExec w (abstract_step c) sig p)
                         c
                         (specification_derive p sig c w)
    = specification_derive (Bind p f) sig c w.
Proof.
  induction p.
  + reflexivity.
  + reflexivity.
  + intros C f' sig' c' w'.
    rewrite specification_derive_assoc.
    rewrite <- (IHp C) .
    rewrite <- H.
    rewrite <- eval_program_assoc.
    rewrite <- exec_abs_assoc.
    rewrite <- (IHp A) .
    reflexivity.
Qed.

Fact abstractExec_Bind
     {W:    Type}
     {I:    Interface}
     {A B:  Type}
     (p:    Program I A)
  : forall (f:    A -> Program I B)
           (sig:  Semantics I)
           (c:    Specification W I)
           (w:    W),
    abstractExec (specification_derive p sig c w)
                 (abstract_step c)
                 (abstractExec w
                               (abstract_step c)
                               sig
                               p)
                 (f (evalProgram sig p))
    = abstractExec w (abstract_step c) sig (Bind p f).
Proof.
  intros f sig c w.
  repeat rewrite abstract_exec_exec_program_same.
  reflexivity.
Qed.

Lemma compliant_correct_compliant
      {W:  Type}
      {I:  Interface}
      {A:  Type}
      (p:  Program I A)
  : forall (c:    Specification W I)
           (w:    W)
           (sig:  Semantics I)
           (H:    sig |= c[w])
           (Hp:   p =| c[w]),
    (abstractExec w (abstract_step c) sig p) |= c[specification_derive p sig c w].
Proof.
  induction p.
  + intros c w sig He Hp;
      apply (pure_compliant_semantics a sig c w He).
  + intros c w sig He Hp;
      apply (correct_effect_compliant_semantics e sig c w He Hp).
  + intros c w sig He Hp.
    inversion Hp;
      apply inj_pair2 in H3;
      repeat apply inj_pair2 in H4;
      subst.
    apply (IHp c w sig He) in Hcp.
    rewrite <- abstractExec_Bind.
    rewrite <- specification_derive_bind.
    apply H.
    ++ exact Hcp.
    ++ apply Hnext.
       exact He.
Qed.

Lemma correct_pbind_correct_left_operand
      {W:    Type}
      {I:    Interface}
      {A B:  Type}
      (w:    W)
      (c:    Specification W I)
      (p:    Program I A)
      (f:    A -> Program I B)
  : Bind p f =| c[w]
    -> p =| c[w].
Proof.
  intros H.
  inversion H; simplify_eqs; simpl_existTs; subst.
  exact Hcp.
Qed.

Lemma correct_bind_correct_right_operand
      {W:     Type}
      {I:     Interface}
      {A B:   Type}
      (w:     W)
      (c:     Specification W I)
      (p:     Program I A)
      (f:     A -> Program I B)
      (sig:   Semantics I)
      (Hsig:  sig |= c[w])
  : Bind p f =| c[w]
    -> f (evalProgram sig p) =| c [specification_derive p sig c w].
Proof.
  intros H.
  inversion H; simplify_eqs; simpl_existTs; subst.
  apply Hnext.
  exact Hsig.
Qed.

Definition no_pre
           {I:  Interface}
           {W:  Type}
           (A:  Type)
           (e:  I A)
           (w:  W)
  : Prop :=
  True.

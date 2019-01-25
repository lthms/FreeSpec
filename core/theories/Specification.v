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
       (I:  Type -> Type)
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

Fact specification_derives_request_eq
     {W:    Type}
     {I:    Interface}
     {A B:  Type}
     (e:    I A)
     (f:    A -> Program I B)
     (sig:  Semantics I)
     (c:    Specification W I)
     (w:    W)
  : specification_derive (Request e f) sig c w
    = specification_derive (f (evalEffect sig e))
                           (execEffect sig e)
                           c
                           (abstract_step c e (evalEffect sig e) w).
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
  cofix _stateful_specification_enforcement.
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
| compliant_pure {A:  Type}
                 (x:  A)
  : correct_program c w (Pure x)
| compliant_request {A B:   Type}
                    (e:     I A)
                    (f:     A -> Program I B)
                    (Hreq:  precondition c e w)
                    (Hnext:  forall (sig: Semantics I)
                                    (Henf: sig |= c[w]),
                        correct_program c
                                        (abstract_step c e (evalEffect sig e) w)
                                        (f (evalEffect sig e)))
  : correct_program c w (Request e f).

Notation "p '=|' c '[' w ']'" :=
  (correct_program c w p)
    (at level 59, no associativity).

(** ** Compliance Preservation

    In order to prove the [compliance_correct_compliance] lemmas, we
    first highlight several convenient properties of
    [compliant_semantics] and [correct_program].

 *)

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
  : specification_derive (pbind (pbind p f) g) sig c w
    = specification_derive (pbind p (fun x => pbind (f x) g)) sig c w.
Proof.
  rewrite program_eq_bind_assoc.
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
    abstractExec w (abstract_step c) sig (pbind p f)
    = abstractExec (specification_derive p sig c w)
                   (abstract_step c)
                   (abstractExec w (abstract_step c) sig p)
                   (f (evalProgram sig p)).
Proof.
  intros B f sig c s.
  repeat rewrite abstract_exec_exec_program_same.
  revert sig; induction p; [reflexivity |]; intros sig.
  apply H.
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
    evalProgram sig (pbind p f)
    = evalProgram (abstractExec w (abstract_step c) sig p)
                  (f (evalProgram sig p)).
Proof.
  intros B f sig c s.
  rewrite abstract_exec_exec_program_same.
  revert sig; induction p; [reflexivity |]; intros sig.
  apply H.
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
    = specification_derive (pbind p f) sig c w.
Proof.
  induction p.
  + reflexivity.
  + intros C f' sig' c' w'.
    apply H.
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
    = abstractExec w (abstract_step c) sig (pbind p f).
Proof.
  intros f sig c w.
  repeat rewrite abstract_exec_exec_program_same.
  rewrite exec_program_bind_assoc.
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
  + intros c w sig He Hp.
    constructor.
    ++ apply H;
         dependent induction Hp.
         +++ now apply He.
         +++ now apply Hnext.
    ++ apply H;
         dependent induction Hp.
       +++ now apply He in Hreq.
       +++ now apply Hnext.
Qed.

Lemma correct_pbind_correct_left_operand
      {W:    Type}
      {I:    Interface}
      {A B:  Type}
      (w:    W)
      (c:    Specification W I)
      (p:    Program I A)
      (f:    A -> Program I B)
  : pbind p f =| c[w]
    -> p =| c[w].
Proof.
  revert w; induction p; intro w.
  + intro.
    constructor.
  + cbn.
    constructor.
    ++ dependent induction H0.
       apply Hreq.
    ++ intros sig Hsig.
       apply H.
       dependent induction H0.
       now apply Hnext.
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
  : pbind p f =| c[w]
    -> f (evalProgram sig p) =| c [specification_derive p sig c w].
Proof.
  revert Hsig;
    revert sig;
    revert w;
    induction p;
    intros w sig Hsig.
  + auto.
  + cbn.
    intro Hc.
    apply H.
    apply Hsig.
    ++ now dependent induction Hc.
    ++ dependent induction Hc.
       now apply Hnext.
Qed.

Definition no_pre
           {I:  Interface}
           {W:  Type}
           (A:  Type)
           (e:  I A)
           (w:  W)
  : Prop :=
  True.

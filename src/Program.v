Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relations.
Require Import Coq.Setoids.Setoid.

Require Import FreeSpec.Tuple.
Require Import FreeSpec.Interp.

Local Open Scope eq_scope.

Require Import FreeSpec.Equiv.
Section PROGRAM.
  Variables (I: Type -> Type).

  Inductive Program (A: Type) :=
  | bind {B: Type}
         (p: Program B)
         (f: B -> Program A)
    : Program A
  | instr (i: I A)
    : Program A
  | ret (a: A)
    : Program A.

  Fixpoint runProgram
           {A: Type}
           (p: Program A)
           (int: Interp I)
    : (A * (Interp I)) :=
    match p with
    | ret _ a => (a, int)
    | instr _ i => interpret i int
    | bind _ p' f => runProgram (f (fst (runProgram p' int))) (snd (runProgram p' int))
    end.

  Definition evalProgram
             {A: Type}
             (p: Program A)
             (int: Interp I)
    : A :=
    fst (runProgram p int).

  Definition execProgram
             {A: Type}
             (p: Program A)
             (int: Interp I)
    : Interp I :=
    snd (runProgram p int).

  CoInductive program_eq
              (i: Interp I)
              {A: Type}
              `{Eq A}
              (p: Program A)
              (p': Program A) :=
  | program_is_eq (Hres: evalProgram p i == evalProgram p' i)
                  (Hnext: execProgram p i == execProgram p' i)
    : program_eq i p p'.

  Lemma program_eq_refl
        (i: Interp I)
    : forall {A: Type}
             `{Eq A}
             (p: Program A),
      program_eq i p p.
  Proof.
    intros A eqA p; constructor; reflexivity.
  Qed.

  Lemma program_eq_sym
        (i: Interp I)
    : forall {A: Type}
             `{Eq A}
             (p p': Program A),
      program_eq i p p'
      -> program_eq i p' p.
  Proof.
    intros A eqA p p' H1.
    destruct H1 as [Hres Hnext].
    constructor; symmetry; assumption.
  Qed.

  Lemma program_eq_trans
        (i: Interp I)
    : forall {A: Type}
             `{Eq A}
             (p p' p'': Program A),
      program_eq i p p'
      -> program_eq i p' p''
      -> program_eq i p p''.
  Proof.
    intros A eqA p p' p'' [Hres1 Hnext1] [Hres2 Hnext2].
    constructor.
    + transitivity (evalProgram p' i); assumption.
    + transitivity (execProgram p' i); assumption.
  Qed.

  Add Parametric Relation
      (int: Interp I)
      (A: Type)
      (eqA: Eq A)
    : (Program A) (@program_eq int A eqA)
      reflexivity proved by (@program_eq_refl int A eqA)
      symmetry proved by (@program_eq_sym int A eqA)
      transitivity proved by (@program_eq_trans int A eqA)
        as program_rel.

  Definition interp_assoc
             (int: Interp I)
    := forall {A B C: Type}
              `{Eq C}
              (p: Program A)
              (f: A -> Program B)
              (g: B -> Program C),
      program_eq int (bind _ (bind _ p f) g) (bind _ p (fun x => bind _ (f x) g)).

  Definition interp_assoc2
             (int: Interp I)
    := forall {A B: Type}
              `{Eq B}
              (p: Program A)
              (f: A -> Program B),
      evalProgram (bind B p f) int
      == evalProgram (f (evalProgram p int)) (execProgram p int).

  Section CONTRACT.
    Definition typeret
               {A: Type}
               (i: I A)
    : Type := A.

    Record Contract :=
      { requirements {A: Type}
                     (i: I A)
        : Prop
      ; promises {A: Type}
                   (i: I A)
        : typeret i -> Prop
      }.

    Variable (c: Contract).

    CoInductive Enforcer
                (int: Interp I)
      : Prop :=
    | enforced (Hprom: forall {A: Type}
                              (i: I A),
                   requirements c i
                   -> (promises c i) (evalInstruction i int))
               (Henf:  forall {A: Type}
                              (i: I A),
                   requirements c i
                   -> Enforcer (execInstruction i int))
      : Enforcer int.

    Section PROGRAM_CONTRACT.
      Inductive contractfull_program
        : forall {A: Type}, Program A -> Type :=
      | contractfull_instr {A: Type}
                           (i: I A)
                           (Hreq: requirements c i)
        : contractfull_program (instr A i)
      | contractfull_ret {A: Type}
                         (a: A)
        : contractfull_program (ret A a)
      | contractfull_inv {A B: Type}
                         (p: Program A)
                         (f: A -> Program B)
                         (Hcp: contractfull_program p)
                         (Hnext: forall (int: Interp I)
                                        (Henf: Enforcer int),
                             contractfull_program (f (evalProgram p int)))
        : contractfull_program (bind B p f).

      Lemma contractfull_instr_enforcement
            {A: Type}
            (i: I A)
        : forall (int: Interp I),
          contractfull_program (instr A i)
          -> Enforcer int
          -> Enforcer (execProgram (instr A i) int).
      Proof.
        intros int Hc Henf.
        destruct Henf as [Hprom Henf].
        apply (Henf A i).
        inversion Hc; simpl_existT; subst.
        exact Hreq.
      Qed.

      Lemma contractfull_ret_enforcement
            {A: Type}
            (a: A)
        : forall (int: Interp I),
          contractfull_program (ret A a)
          -> Enforcer int
          -> Enforcer (execProgram (ret A a) int).
      Proof.
        intros int Hc Henf.
        exact Henf.
      Qed.

      Lemma contractfull_program_enforcement
            {A B: Type}
            (p: Program A)
        : forall (int: Interp I),
          contractfull_program p
          -> Enforcer int
          -> Enforcer (execProgram p int).
      Proof.
        induction p.
        + intros int Hc Henf.
          assert (contractfull_program (f (evalProgram p int))) as Hc'.
          ++ inversion Hc; repeat simpl_existT; subst.
             apply (Hnext int Henf).
          ++ inversion Hc; repeat simpl_existT; subst.
             apply H with (int := execProgram p int) in Hc'.
             exact Hc'.
             apply IHp; [ exact Hcp
                       | exact Henf
                       ].
        + apply contractfull_instr_enforcement.
        + apply contractfull_ret_enforcement.
      Qed.
    End PROGRAM_CONTRACT.
  End CONTRACT.

  Section MAKE_INTERP.
    Variables (State: Type).

    Definition PS
      := forall {A: Type}, State -> I A -> (A * State).

    CoFixpoint mkInterp
               (ps: PS)
               (s: State)
      : Interp I :=
      interp (
          fun (A: Type)
              (p: I A) =>
            (fst  (ps A s p), mkInterp ps (snd (ps A s p)))).

    Lemma mkInterp_is_assoc
          (ps: PS)
          (s: State)
      : interp_assoc (mkInterp ps s).
    Proof.
      unfold interp_assoc.
      intros A B C p f g.
      induction p; (constructor; [ reflexivity | apply interp_eq_refl]).
    Qed.

    Lemma mkInterp_is_assoc2
          (ps: PS)
          (s: State)
      : interp_assoc2 (mkInterp ps s).
    Proof.
      unfold interp_assoc2.
      intros A B p f.
      induction p; reflexivity.
    Qed.

    Section STATEFUL_INTERP_ENFORCER.
      Variables (step: PS)
                (inv: State -> Prop)
                (c: Contract).

      Definition contract_preserves_inv
        := forall {A: Type}
                  (i: I A)
                  (s: State),
           inv s
           -> requirements c i
           -> inv (snd (step A s i)).

      Definition contract_enforces_promises
        := forall {A: Type}
                  (i: I A)
                  (s: State),
          inv s
          -> requirements c i
          -> promises c i (fst (step A s i)).

      Lemma stateful_contract_enforcement
            (Hpres: contract_preserves_inv)
            (Henf: contract_enforces_promises)
        : forall (s: State), inv s -> Enforcer c (mkInterp step s).
      Proof.
        cofix.
        intros s Hinv.
        split; intros A i Hreq; cbn.
        + apply (Henf A i s Hinv Hreq).
        + apply (Hpres A i s) in Hinv.
          ++ apply (stateful_contract_enforcement  (snd (step A s i)) Hinv).
          ++ exact Hreq.
      Qed.
    End STATEFUL_INTERP_ENFORCER.
  End MAKE_INTERP.
End PROGRAM.

Arguments bind [I A B] (p f).
Arguments instr [I A] (i).
Arguments ret [I A] (a).

Arguments mkInterp [I State] (ps s).

Arguments runProgram [I A] (p int).
Arguments execProgram [I A] (p int).
Arguments evalProgram [I A] (p int).

Arguments typeret [I A] (i).
Arguments Enforcer [I] (c int).

Arguments stateful_contract_enforcement [I State] (step inv c Hpres Henf s).
Arguments contract_enforces_promises [I State] (step inv c).
Arguments contract_preserves_inv [I State] (step inv c).

Arguments contractfull_program [I] c [A].

Notation "int <· p" := (fst (runProgram int p)) (at level 50) : prog_scope.
Notation "p >>= f" := (bind p f) (at level 50) : prog_scope.
Notation "a <- p ; q" :=
  (bind p (fun a => q)) (at level 60, right associativity, p at next level)
  : prog_scope.
Notation "[ i ]" := (instr i) (at level 50) : prog_scope.
Notation "· a" := (ret a) (at level 50) : prog_scope.

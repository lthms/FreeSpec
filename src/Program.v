Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.
Require Import Coq.Relations.Relations.
Require Import Coq.Setoids.Setoid.

Section PROGRAM.
  Variables (Instruction: Type -> Type).

  Inductive Program (A: Type) :=
  | bind {B: Type}
         (p: Program B)
         (f: B -> Program A)
    : Program A
  | instr (i: Instruction A)
    : Program A
  | ret (a: A)
    : Program A.

  Section INTERP.
    CoInductive Interp: Type :=
    | interp (f: forall {A: Type}, Instruction A -> (A * Interp))
      : Interp.

    Section DO_INTERP.
      Definition interpret
                 {A: Type}
                 (int: Interp)
                 (i: Instruction A)
      : (A * Interp) :=
        match int with interp f => f A i end.

      Fixpoint runProgram
               {A: Type}
               (int: Interp)
               (p: Program A)
        : (A * Interp) :=
        match p with
        | ret _ a => (a, int)
        | instr _ i => interpret int i
        | bind _ p' f => runProgram (snd (runProgram int p')) (f (fst (runProgram int p')))
        end.
    End DO_INTERP.

    CoInductive interp_eq
                (i1: Interp)
                (i2: Interp)
      : Prop :=
    | interp_is_eq (Hres: forall {A: Type}
                                 {p: Instruction A},
                       fst (interpret i1 p) = fst (interpret i2 p))
                   (Hnext: forall {A: Type}
                                  {p: Instruction A},
                       interp_eq (snd (interpret i1 p)) (snd (interpret i2 p)))
      : interp_eq i1 i2.

    Lemma interp_eq_refl
      : forall (i: Interp), interp_eq i i.
    Proof.
      cofix.
      intro i.
      constructor.
      + reflexivity.
      + intros A p.
        apply interp_eq_refl.
    Qed.

    Lemma interp_eq_sym
      : forall (i i': Interp), interp_eq i i' -> interp_eq i' i.
    Proof.
      cofix.
      intros i i' H1.
      destruct H1.
      constructor.
      + intros A p.
        symmetry.
        exact (Hres A p).
      + intros A p.
        apply (interp_eq_sym (snd (interpret i p)) (snd (interpret i' p)) (Hnext A p)).
    Qed.

    Lemma interp_eq_trans
      : forall (i i' i'': Interp),
        interp_eq i i'
        -> interp_eq i' i''
        -> interp_eq i i''.
    Proof.
      cofix.
      intros i i' i'' H1 H2.
      destruct H1 as [Hres1 Hnext1].
      destruct H2 as [Hres2 Hnext2].
      constructor.
      + intros A p.
        rewrite <- (Hres2 A p).
        exact (Hres1 A p).
      + intros A p.
        apply (interp_eq_trans (snd (interpret i p))
                               (snd (interpret i' p))
                               (snd (interpret i'' p))
                               (Hnext1 A p)
                               (Hnext2 A p)).
    Qed.

    Add Parametric Relation : (Interp) (interp_eq)
      reflexivity proved by (interp_eq_refl)
      symmetry proved by (interp_eq_sym)
      transitivity proved by (interp_eq_trans)
        as interp_rel.

    Require Import Morphisms.

    Definition interp_ret_eq
               {A: Type}
               (x: (A * Interp))
               (y: (A * Interp))
      : Prop :=
      fst x = fst y /\ interp_eq (snd x) (snd y).

    Lemma interp_ret_eq_refl
          {A: Type}
          (x: (A * Interp))
      : interp_ret_eq x x.
    Proof.
      split; reflexivity.
    Qed.

    Lemma interp_ret_eq_sym
          {A: Type}
          (x: (A * Interp))
          (y: (A * Interp))
      : interp_ret_eq x y -> interp_ret_eq y x.
    Proof.
      intros [H1 H2].
      split; symmetry; assumption.
    Qed.

    Lemma interp_ret_eq_trans
          {A: Type}
          (x: (A * Interp))
          (y: (A * Interp))
          (z: (A * Interp))
      : interp_ret_eq x y
        -> interp_ret_eq y z
        -> interp_ret_eq x z.
    Proof.
      intros [H1 H2] [H1' H2'].
      split.
      + transitivity (fst y); assumption.
      + transitivity (snd y); assumption.
    Qed.

    Add Parametric Relation (A: Type) : (A * Interp) (@interp_ret_eq A)
      reflexivity proved by (interp_ret_eq_refl)
      symmetry proved by (interp_ret_eq_sym)
      transitivity proved by (interp_ret_eq_trans)
        as interp_ret_rel.

    Add Parametric Morphism
        (A: Type): (@snd A Interp)
        with signature (@interp_ret_eq A) ==> (interp_eq)
          as snd_interp_ret.
    Proof.
      intros [a int] [b int'] [Heq1 Heq2].
      exact Heq2.
    Qed.

    Add Parametric Morphism
        (A: Type): (@fst A Interp)
        with signature (@interp_ret_eq A) ==> (@eq A)
          as fst_interp_ret.
    Proof.
      intros [a int] [b int'] [Heq1 Heq2].
      exact Heq1.
    Qed.

    Add Parametric Morphism
        (A: Type) (i: Instruction A): (fun int => snd (interpret int i))
        with signature (@interp_eq) ==> (@interp_eq)
          as interp_morph.
    Proof.
      intros int int' Heq.
      destruct Heq as [H1 H2].
      apply H2.
    Qed.

    Add Parametric Morphism
        (A: Type) (i: Instruction A): (fun int => fst (interpret int i))
        with signature (@interp_eq) ==> (@eq A)
          as interp_res_morph.
    Proof.
      intros int int' Heq.
      destruct Heq as [H1 H2].
      apply H1.
    Qed.

    Add Parametric Morphism
        (A: Type) (p: Program A): (fun int => snd (runProgram int p))
        with signature (@interp_eq) ==> (@interp_eq)
          as runProgram_morph.
    Proof.
      intros int int' Heq.
      induction p.
      + admit.
      + destruct Heq as [H1 H2];
          cbn;
          apply H2.
      + cbn; exact Heq.
    Admitted.

    Add Parametric Morphism
        (A: Type) (p: Program A): (fun int => fst (runProgram int p))
        with signature (@interp_eq) ==> (@eq A)
          as runProgram_ret_morph.
    Proof.
      intros int int' Heq.
      induction p.
      + admit.
      + destruct Heq as [H1 H2];
          cbn;
          apply H1.
      + cbn; reflexivity.
    Admitted.

    CoInductive program_eq
                (i: Interp)
                {A: Type}
                (p: Program A)
                (p': Program A) :=
    | program_is_eq (Hres: fst (runProgram i p) = fst (runProgram i p'))
                    (Hnext: interp_eq (snd (runProgram i p)) (snd (runProgram i p'))): program_eq i p p'.

    Lemma program_eq_refl
          (i: Interp)
      : forall {A: Type} (p: Program A), program_eq i p p.
    Proof.
      intro A.
      cofix.
      intro p.
      constructor.
      + reflexivity.
      + apply interp_eq_refl.
    Qed.

    Lemma program_eq_sym
          (i: Interp)
      : forall {A: Type}
               (p p': Program A),
        program_eq i p p'
        -> program_eq i p' p.
    Proof.
      intro A.
      cofix.
      intros p p' H1.
      destruct H1 as [Hres Hnext].
      constructor.
      + symmetry; exact Hres.
      + apply (interp_eq_sym (snd (runProgram i p))
                             (snd (runProgram i p'))
                             Hnext).
    Qed.

    Lemma program_eq_trans
          (i: Interp)
      : forall {A: Type}
               (p p' p'': Program A),
        program_eq i p p'
        -> program_eq i p' p''
        -> program_eq i p p''.
    Proof.
      intro A.
      cofix.
      intros p p' p'' [Hres1 Hnext1] [Hres2 Hnext2].
      constructor.
      + rewrite <- Hres2; exact Hres1.
      + apply (interp_eq_trans (snd (runProgram i p))
                               (snd (runProgram i p'))
                               (snd (runProgram i p''))
                               Hnext1
                               Hnext2).
    Qed.

    Definition interp_assoc
               (int: Interp)
      := forall {A B C: Type}
                (p: Program A)
                (f: A -> Program B)
                (g: B -> Program C),
        program_eq int (bind _ (bind _ p f) g) (bind _ p (fun x => bind _ (f x) g)).

    Definition interp_assoc2
               (int: Interp)
      := forall {A B: Type}
                (p: Program A)
                (f: A -> Program B),
        fst (runProgram int (bind _ p f))
        = fst (runProgram (snd (runProgram int p)) (f (fst (runProgram int p)))).

  End INTERP.

  Section CONTRACT.
    Definition typeret
               {A: Type}
               (i: Instruction A)
    : Type := A.

    Record Contract :=
      { requirements {A: Type}
                     (i: Instruction A)
        : Prop
      ; promises {A: Type}
                 (i: Instruction A)
        : typeret i -> Prop
     }.

    Variable (c: Contract).

    CoInductive Enforcer
                (int: Interp)
      : Prop :=
    | enforced (Hprom: forall {A: Type}
                              (i: Instruction A),
                   requirements c i
                   -> (promises c i) (fst (interpret int i)))
               (Henf:  forall {A: Type}
                              (i: Instruction A),
                   requirements c i
                   -> Enforcer (snd (interpret int i)))
      : Enforcer int.

    Section PROGRAM_CONTRACT.
      Inductive contractfull_program
        : forall {A: Type}, Program A -> Type :=
      | contractfull_instr {A: Type}
                           (i: Instruction A)
                           (Hreq: requirements c i)
        : contractfull_program (instr A i)
      | contractfull_ret {A: Type}
                         (a: A)
        : contractfull_program (ret A a)
      | contractfull_inv {A B: Type}
                         (p: Program A)
                         (f: A -> Program B)
                         (Hcp: contractfull_program p)
                         (Hnext: forall (int: Interp)
                                        (Henf: Enforcer int),
                             contractfull_program (f (fst (runProgram int p))))
        : contractfull_program (bind B p f).

      Lemma contractfull_instr_enforcement
            {A: Type}
            (i: Instruction A)
        : forall (int: Interp),
          contractfull_program (instr A i)
          -> Enforcer int
          -> Enforcer (snd (runProgram int (instr A i))).
      Proof.
        intros int Hc Henf.
        cbn in *.
        destruct Henf as [Hprom Henf].
        apply (Henf A i).
        inversion Hc; simpl_existT; subst.
        exact Hreq.
      Qed.

      Lemma contractfull_ret_enforcement
            {A: Type}
            (a: A)
        : forall (int: Interp),
          contractfull_program (ret A a)
          -> Enforcer int
          -> Enforcer (snd (runProgram int (ret A a))).
      Proof.
        intros int Hc Henf.
        cbn in *.
        exact Henf.
      Qed.

      Lemma contractfull_program_enforcement
            {A B: Type}
            (p: Program A)
        : forall (int: Interp),
          contractfull_program p
          -> Enforcer int
          -> Enforcer (snd (runProgram int p)).
      Proof.
        induction p.
        + intros int Hc Henf.
          assert (contractfull_program (f (fst (runProgram int p)))) as Hc'.
          * inversion Hc; repeat simpl_existT; subst.
            apply (Hnext int Henf).
          * inversion Hc; repeat simpl_existT; subst.
            apply H with (int:=snd (runProgram int p)) in Hc'.
            cbn.
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
      := forall {A: Type}, State -> Instruction A -> (A * State).

    CoFixpoint mkInterp
               (ps: PS)
               (s: State)
      : Interp :=
      interp (
          fun (A: Type)
              (p: Instruction A) =>
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
                  (i: Instruction A)
                  (s: State),
           inv s
           -> requirements c i
           -> inv (snd (step A s i)).

      Definition contract_enforces_promises
        := forall {A: Type}
                  (i: Instruction A)
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
          - apply (stateful_contract_enforcement  (snd (step A s i)) Hinv).
          - exact Hreq.
      Qed.
    End STATEFUL_INTERP_ENFORCER.
  End MAKE_INTERP.
End PROGRAM.

Arguments bind [Instruction A B] (p f).
Arguments instr [Instruction A] (i).
Arguments ret [Instruction A] (a).

Arguments mkInterp [Instruction State] (ps s).

Arguments interpret [Instruction A] (int i).
Arguments runProgram [Instruction A] (int p).

Arguments typeret [Instruction A] (i).
Arguments Enforcer [Instruction] (c int).

Arguments stateful_contract_enforcement [Instruction State] (step inv c Hpres Henf s).
Arguments contract_enforces_promises [Instruction State] (step inv c).
Arguments contract_preserves_inv [Instruction State] (step inv c).

Arguments contractfull_program [Instruction] c [A].

Notation "int <· p" := (fst (runProgram int p)) (at level 50) : prog_scope.
Notation "p >>= f" := (bind p f) (at level 50) : prog_scope.
Notation "a <- p ; q" :=
  (bind p (fun a => q)) (at level 60, right associativity, p at next level)
  : prog_scope.
Notation "[ i ]" := (instr i) (at level 50) : prog_scope.
Notation "· a" := (ret a) (at level 50) : prog_scope.

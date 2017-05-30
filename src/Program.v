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
    | interp (f: forall {A: Type}, Program A -> (A * Interp))
      : Interp.

    Section DO_INTERP.
      Definition interpret
                 {A: Type}
                 (int: Interp)
                 (p: Program A)
      : (A * Interp) :=
        match int with
        | interp f => f A p
        end.
    End DO_INTERP.

    CoInductive interp_eq
                (i1: Interp)
                (i2: Interp)
      : Prop :=
    | interp_is_eq (Hres: forall {A: Type}
                                 {p: Program A},
                       fst (interpret i1 p) = fst (interpret i2 p))
                   (Hnext: forall {A: Type}
                                  {p: Program A},
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

    CoInductive program_eq
                (i: Interp)
                {A: Type}
                (p: Program A)
                (p': Program A) :=
    | program_is_eq (Hres: fst (interpret i p) = fst (interpret i p'))
                    (Hnext: interp_eq (snd (interpret i p)) (snd (interpret i p'))): program_eq i p p'.

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
      + apply (interp_eq_sym (snd (interpret i p))
                             (snd (interpret i p'))
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
      + apply (interp_eq_trans (snd (interpret i p))
                               (snd (interpret i p'))
                               (snd (interpret i p''))
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
        fst (interpret int (bind _ p f))
        = fst (interpret (snd (interpret int p)) (f (fst (interpret int p)))).

  End INTERP.

  Section MAKE_INTERP.
    Variables (State: Type).

    Definition PS
      := forall {A: Type}, State -> Instruction A -> (A * State).

    Fixpoint s_interp
             (ps: PS)
             (s: State)
             {A: Type}
             (p: Program A)
      : (A * State) :=
      match p with
      | ret _ a => (a, s)
      | instr _ i => ps A s i
      | bind _ p' f => s_interp ps (snd (s_interp ps s p')) (f (fst (s_interp ps s p')))
      end.

    CoFixpoint mkInterp
               (ps: PS)
               (s: State)
      : Interp :=
      interp (
          fun (A: Type)
              (p: Program A) =>
            (fst (s_interp ps s p), mkInterp ps (snd (s_interp ps s p)))).

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
  End MAKE_INTERP.

  Section CONTRACT.
    Record Contract :=
     { requirements (A: Type): Instruction A -> Prop
     ; promises (A: Type): Instruction A -> (A -> Prop)
     }.

    CoInductive Enforcer
                (c: Contract)
                (int: Interp)
      : Prop :=
    | enforced (Hproof: forall {A: Type}
                               (i: Instruction A),
                   requirements c A i
                   -> (promises c A i) (fst (interpret int (instr A i)))
                      /\ Enforcer c (snd (interpret int (instr A i))))
      : Enforcer c int.
  End CONTRACT.
End PROGRAM.

Arguments bind [Instruction A B] (p f).
Arguments instr [Instruction A] (i).
Arguments ret [Instruction A] (a).

Arguments mkInterp [Instruction State] (ps s).

Arguments interpret [Instruction A] (int p).

Notation "int <· p" := (fst (interpret int p)) (at level 50) : prog_scope.
Notation "p >>= f" := (bind p f) (at level 50) : prog_scope.
Notation "a <- p ; q" :=
  (bind p (fun a => q)) (at level 60, right associativity, p at next level)
  : prog_scope.
Notation "[ i ]" := (instr i) (at level 50) : prog_scope.
Notation "· a" := (ret a) (at level 50) : prog_scope.

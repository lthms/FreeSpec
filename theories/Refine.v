Require Import FreeSpec.Program.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Contract.
Require Import FreeSpec.Abstract.

(** * Stateful Refinement

    ** Definition
 *)

Definition StatefulRefinement
           (Ii: Type -> Type)
           (Io: Type -> Type)
           (S:  Type) :=
  forall (A: Type),
    Ii A -> S -> Program Io (A * S).

Definition StatefulInterpret
           {Ii: Type -> Type}
           {Io: Type -> Type}
           {S:  Type}
           (sr: StatefulRefinement Ii Io S)
           (s: S)
           (int: Interp Io)
  : Interp Ii :=
    mkInterp (fun {A: Type}
                  (st: (S * Interp Io))
                  (i: Ii A)
              => (fst (evalProgram (snd st) (sr A i (fst st))),
                  (snd (evalProgram (snd st) (sr A i (fst st))),
                   (execProgram (snd st) (sr A i (fst st))))))
             (s, int).

(** ** Contract Enforcement

    We consider so-called “predicates of synchronization” between two
    abstract States [Si] (input) and [So] (output) linked by a
    concrete state [S].
 *)

Definition sync_pred
           (Si So: Type)
           (S: Type)
  := Si -> S -> So -> Type.

Definition compliant_refinement
           {Si So: Type}
           {Ii Io: Interface}
           {S: Type}
           (sr: StatefulRefinement Ii Io S)
           (master: Contract Si Ii)
           (slave: Contract So Io)
           (sync: sync_pred Si So S) :=
  forall (si: Si)
         (s: S)
         (so: So)
         {A: Type}
         (i: Ii A),
    sync si s so
    -> requirements master i si
    -> contractfull_program slave so (sr A i s).

Definition sync_preservation
           {Si So: Type}
           {Ii Io: Interface}
           {S: Type}
           (sr: StatefulRefinement Ii Io S)
           (master: Contract Si Ii)
           (slave: Contract So Io)
           (sync: sync_pred Si So S) :=
  forall (si: Si)
         (s: S)
         (so: So)
         (int: Interp Io)
         (Henf: Enforcer int slave so)
         {A: Type}
         (i: Ii A),
  sync si s so
  -> requirements master i si
  -> sync (abstract_step master i (fst (evalProgram int (sr A i s))) si)
          (snd (evalProgram int (sr A i s)))
          (contract_derive (sr A i s) int slave so).

Definition sync_promises
           {Si So: Type}
           {Ii Io: Interface}
           {S: Type}
           (sr: StatefulRefinement Ii Io S)
           (master: Contract Si Ii)
           (slave: Contract So Io)
           (sync: sync_pred Si So S) :=
  forall (si: Si)
         (s: S)
         (so: So)
         (int: Interp Io)
         (Henf: Enforcer int slave so)
         {A: Type}
         (i: Ii A),
  sync si s so
  -> requirements master i si
  -> promises master i (fst (evalProgram int (sr A i s))) si.

Theorem enforcer_refinement
        {Si So: Type}
        {Ii Io: Interface}
        {S: Type}
        (sr: StatefulRefinement Ii Io S)
        (master: Contract Si Ii)
        (slave: Contract So Io)
        (sync: sync_pred Si So S)
        (Hsyncpres: sync_preservation sr master slave sync)
        (Hsyncp: sync_promises sr master slave sync)
        (Hcompliant: compliant_refinement sr master slave sync)
  : forall (si: Si)
           (s: S)
           (so: So)
           (int: Interp Io)
           (Henf: Enforcer int slave so),
    sync si s so
    -> Enforcer (StatefulInterpret sr s int) master si.
Proof.
  cofix.
  intros si s so int Henf Hsync.
  constructor.
  + intros A i Hreq.
    unfold sync_promises in Hsyncp.
    assert (evalInstruction (StatefulInterpret sr s int) i = fst (evalProgram int (sr A i s)))
      as Heq by reflexivity.
    rewrite Heq.
    apply (Hsyncp si s so int Henf A i Hsync Hreq).
  + intros A i Hreq.
    unfold compliant_refinement in Hcompliant.
    assert (contractfull_program slave so (sr A i s))
      as Hcp
        by  apply (Hcompliant si s so A i Hsync Hreq).
    assert (execInstruction (StatefulInterpret sr s int) i
            = StatefulInterpret sr
                                (snd (evalProgram int (sr A i s)))
                                (execProgram int (sr A i s)))
      as Hassoc
        by reflexivity.
    rewrite Hassoc.
    apply (enforcer_refinement _ _ (contract_derive (sr A i s) int slave so)).
    ++ rewrite <- (abstract_exec_exec_program_same (sr A i s)
                                                   so
                                                   (abstract_step slave)
                                                   int).
       apply (enforcer_contractfull_enforcer _ _ _ int Henf Hcp).
    ++ apply Hsyncpres.
       +++ exact Henf.
       +++ exact Hsync.
       +++ exact Hreq.
Qed.

(** * Pure Refinement

 *)

Definition PureRefinement
           (Ii: Type -> Type)
           (Io: Type -> Type)
  := forall (A: Type),
    Ii A -> Program Io A.
Require Import FreeSpec.Program.

Section REFINEMENT.
  Parameters (Ii: Type -> Type)
             (Io: Type -> Type)
             (S:  Type).

  Definition StatefulRefinement
    := forall {A: Type},
    Ii A -> S -> Program Io (A * S).

  Definition StatefulInterpret
             (sr: StatefulRefinement)
             (s: S)
             (int: Interp Io)
    : Interp Ii :=
    mkInterp (fun {A: Type}
                  (st: (S * Interp Io))
                  (i: Ii A)
              => (fst (fst (interpret (snd st) (sr A i (fst st)))),
                  (snd (fst (interpret (snd st) (sr A i (fst st)))),
                   (snd (interpret (snd st) (sr A i (fst st)))))))
             (s, int).

  Definition PureRefinement
             (Ii: Type -> Type)
             (Io: Type -> Type)
    := forall (A: Type),
      Ii A -> Program Io A.
End REFINEMENT.
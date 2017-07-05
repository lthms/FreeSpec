Require Import FreeSpec.Program.
Require Import FreeSpec.Interp.

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

Definition PureRefinement
           (Ii: Type -> Type)
           (Io: Type -> Type)
  := forall (A: Type),
    Ii A -> Program Io A.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Program.
Require Import FreeSpec.Refine.
Require Import FreeSpec.Control.Classes.
Require Import FreeSpec.Control.State.
Require Import FreeSpec.WEq.

Set Implicit Arguments.

Section PROXY.
  Variables (I Ii Io:     Interface)
            (S:           Type)
            (proxy:       StatefulRefinement Ii Io S)
            (to_proxy:    forall (A:  Type), I A -> option (Ii A))
            (from_proxy:  PureRefinement Io I).

  Definition proxy_aux
             {A:           Type}
             (int:         Interp I)
             (s:           S)
             (i:           I A)
    : (A * S * Interp I) :=
    match to_proxy i with
    | None
      => (evalInstruction int i, s, execInstruction int i)
    | Some i
      => runProgram int (refine (proxy i s) from_proxy)
    end.

  CoFixpoint proxify
             (int:  Interp I)
             (s:    S)
    : Interp I :=
    interp (fun (A:  Type)
                (i:  I A)
            => ( fst (fst (proxy_aux int s i))
               , proxify (snd (proxy_aux int s i))
                         (snd (fst (proxy_aux int s i)))
               )
           ).
End PROXY.
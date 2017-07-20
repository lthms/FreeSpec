Require Import FreeSpec.Control.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Interp.
Require Import FreeSpec.State.

Class MonadInterp
      (I: Interface)
      (M: Type -> Type) :=
  { monadinterp_is_monad :> Monad M
  ; interpret (A: Type): I A -> M A
  }.

Arguments interpret [I M _ A] (_).

CoFixpoint monad_state_interp
           {I: Interface}
           {S: Type}
          `{MonadInterp I (State S)}
           (init: S)
  : Interp I :=
  mkInterp (fun (A: Type)
                (s: S)
                (i: I A)
            => runState (interpret i) s)
           init.

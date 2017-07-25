Require Import FreeSpec.Control.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Control.State.
Require Import FreeSpec.WEq.
Require Import FreeSpec.Control.Identity.

(** * The Interpreter Monad

  We define a monadic interface for Interpreter. The long term goal is
  to deprecate [Interp] in favor of [MonadInterp]. In case of success,
  it would be a lot more easy to use FreeSpec along with Haskell, as
  an interpreter could be implemented thanks to the IO monad.

  Currently, the main challenge which prevents use to use
  [MonadInterp] is the notion of interpreter equivalence (see
  [interp_eq]).

 *)

Class MonadInterp
      (I: Interface)
      (M: Type -> Type) :=
  { monadinterp_is_monad :> Monad M
  ; interpret (A: Type): I A -> M A
  }.

Arguments interpret [I M _ A] (_).

(** * Another Stateful Interpreter

    Until we find a way to deprecate [Interp] in favor of
    [MonadInterp], we can use the State monad to build stateful
    interpreters quite easily.

 *)

Definition monad_state_interp
           {I: Interface}
           {S: Type}
          `{WEq S}
          `{MonadInterp I (State S)}
           (init: S)
  : Interp I :=
  mkInterp (fun (A: Type)
                (s: S)
                (i: I A)
            => unwrap (runStateT (m:=Identity) (interpret i) s))
           init.

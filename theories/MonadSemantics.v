Require Import FreeSpec.Control.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Control.State.
Require Import FreeSpec.WEq.
Require Import FreeSpec.Control.Identity.

(** * The Semantics Monad

  We define a monadic interface for Semantics. This allows for
  implementing a semantics thanks to the [Control.IO]
  Monad. Unfortunately, the FreeSpec formalism is not quite ready for
  this interface.

 *)

Class MonadSemantics
      (I:  Interface)
      (M:  Type -> Type) :=
  { monadsemantics_is_monad :> Monad M
  ; handle (A: Type):  I A -> M A
  }.

Arguments handle [I M _ A] (_).

(** * Another Stateful Semantics

    Until we find a way to deprecate [Semantics] in favor of
    [MonadSemantics], we can use the State monad to build stateful
    semantics quite easily.

 *)

Definition monad_state_semantics
           {S:     Type} `{WEq S}
           {I:     Interface} `{MonadSemantics I (State S)}
           (init:  S)
  : Semantics I :=
  mkSemantics (fun (A:  Type)
                   (s:  S)
                   (e:  I A)
               => unwrap (runStateT (m:=Identity) (handle e) s))
              init.

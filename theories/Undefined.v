Require Import FreeSpec.Interface.
Require Import FreeSpec.Program.
Require Import FreeSpec.Compose.
Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Classes.

(** * The Shameful [Undefined] Interface

    Using the [Undefined] interface, you can pledge guilty of having
    undefined behaviour in your formal specification.

    ** Definition

    *)

Inductive Undefined
  : Interface :=
| undefined {A: Type}
  : Undefined A.

(** ** Why using an Interface?

    We use an Interface to deal with Undefined Behaviour for at least
    two reasons:

      * It makes obvious that a given Semantics uses the [undefined]
        effect
      * It is easier to write a specification to check if [undefined]
        is called

    * [UndefMonad] Typeclass

    The UndefMonad is here to provide an easier way to work with
    undefined behaviour. Indeed, this library provides the required
    typeclass instances so that if the [Undefined] Interface is used,
    the [undef] primitive is available on the top of the monad stack
    (that is, after the composition of the Interfaces and the use of a
    State Monad).
 *)

Class UndefMonad
      (m: Type -> Type)
  := { undef_is_monad :> Monad m
     ; undef {A: Type}
       : m A
     }.

Instance undefmonad_Trans
         (t: forall (m: Type -> Type) `{Monad m}, Type -> Type)
        `{MonadTrans t}
         (m: Type -> Type)
        `{UndefMonad m}
  : UndefMonad (t m) :=
  { undef := fun {a: Type} => lift (undef (A:=a))
  }.

Instance undefprogram_UndefMonad
  : UndefMonad (Program Undefined) :=
  { undef := fun {a: Type} => Request (undefined (A:=a))
  }.

Local Open Scope free_scope.

Instance rightprogram_UndefMonad
         {I I': Interface}
        `{UndefMonad (Program I)}
  : UndefMonad (Program (I <+> I')) :=
  { undef := fun {a: Type} => liftl undef
  }.

Instance leftprogram_UndefMonad
         {I I': Interface}
        `{UndefMonad (Program I')}
  : UndefMonad (Program (I <+> I')) :=
  { undef := fun {a: Type} => liftr undef
  }.
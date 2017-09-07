Require Import FreeSpec.Control.
Require Import FreeSpec.WEq.
Require Import FreeSpec.Control.IO.
Require Import Coq.Strings.String.

Local Open Scope free_control_scope.
Local Open Scope string_scope.

Axiom (putStrLn: string -> IO unit).

Definition coq_main
  : IO unit :=
  putStrLn "hello"                                                  ;;
  putStrLn "world".
Require Import Coq.Strings.String.
Require Import FreeSpec.Stdlib.Console.
Require Import FreeSpec.Program.
Require Import FreeSpec.Compose.
Require Import Prelude.Control.

Local Open Scope prelude_scope.

Definition hello {ix} `{Use Console.i ix} : Program ix unit :=
  Console.echo "Hello, world".

Exec hello.


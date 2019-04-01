Require Import Prelude.Control.

Require Import FreeSpec.Program.
Require Import FreeSpec.Exec.
Require Import FreeSpec.Stdlib.Env.
Require Import FreeSpec.Stdlib.Console.

Require Import Coq.ZArith.ZArith.

#[local]
Open Scope prelude_scope.
#[local]
Open Scope Z_scope.

Definition echo_arg
           {ix} `{Use Console.i ix, Use Args.i ix}
  : Program ix unit :=
  argc <- Args.count;
  if argc =? 1
  then (Args.get 0 >>= Console.echo)
  else Console.echo
         "usage: FREESPEC_EXEC_ARGC=1 FREESPEC_EXEC_ARGV_0=<text> coqc examples/echo.v".

Exec (withArgs echo_arg).

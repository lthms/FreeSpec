From FreeSpec Require Import Core Args Console.
From Coq Require Import ZArith.

Generalizable All Variables.

#[local]
Open Scope Z_scope.

Definition echo_arg `{Provide ix CONSOLE, Provide ix ARGS} : impure ix unit :=
  do let* argc := arg_count in
     if argc =? 1
     then arg_value 0 >>= Console.echo
     else echo
         "usage: FREESPEC_EXEC_ARGC=1 FREESPEC_EXEC_ARGV_0=<text> coqc examples/echo.v"
  end.

Exec (with_args echo_arg).

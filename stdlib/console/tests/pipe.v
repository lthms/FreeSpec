From FreeSpec Require Import Exec Console.

Generalizable All Variables.

Definition pipe `{ix :| CONSOLE} : impure ix unit :=
  scan >>= echo.

Exec pipe.

From FreeSpec Require Import Exec Console.

Generalizable All Variables.

Definition pipe `{Provide ix CONSOLE} : impure ix unit :=
  scan >>= echo.

Exec pipe.

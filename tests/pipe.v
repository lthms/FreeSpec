From FreeSpec.Exec Require Import All.
From FreeSpec.Stdlib Require Import Console.

Generalizable All Variables.

Definition pipe `{Provide ix CONSOLE} : impure ix unit :=
  scan >>= echo.

Exec pipe.

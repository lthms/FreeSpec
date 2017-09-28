Require Import FreeSpec.Control.
Require Import FreeSpec.Control.IO.

Require Import FreeSpec.Specs.x86.MCH.MCH.

Definition x86Main
  : IO unit :=
  pure tt.
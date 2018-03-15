Require Import FreeSpec.Interface.
Require Import FreeSpec.Arch.Memory.
Require Import FreeSpec.Arch.Address.

Require Import Prelude.Equality.

Local Open Scope prelude_scope.

Definition Abstract
  : Type :=
  address -> byte.

Definition update
           (a:    address)
           (v:    byte)
           (map:  Abstract)
  : Abstract :=
  fun (a':  address)
  => if a ?= a'
     then v
     else map a'.

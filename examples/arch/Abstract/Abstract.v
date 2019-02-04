Require Import FreeSpec.Interface.
Require Import FreeSpec.Arch.Memory.
Require Import FreeSpec.Arch.Address.

Require Import Prelude.Equality.

Local Open Scope prelude_scope.

Definition View
  : Type :=
  address -> byte.

Definition update
           (a:    address)
           (v:    byte)
           (map:  View)
  : View :=
  fun (a':  address)
  => if a ?= a'
     then v
     else map a'.

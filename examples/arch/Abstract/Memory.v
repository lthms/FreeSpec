Require Import FreeSpec.Interface.
Require Import FreeSpec.Arch.Memory.
Require Import FreeSpec.Arch.Address.

Inductive Memory_interface
  : Interface :=
| read_mem (addr:  address)
  : Memory_interface byte
| write_mem (addr:  address)
            (val:   byte)
  : Memory_interface unit.

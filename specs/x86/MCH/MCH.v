Require Import FreeSpec.Specs.x86.MCH.SMRAMC.
Require Import FreeSpec.Specs.Memory.
Require Import FreeSpec.Specs.Address.
Require Import FreeSpec.Interface.

Inductive MCHi
  : Interface :=
| PIO_in (port: word)
  : MCHi byte
| PIO_out (port: word)
          (val:  byte)
  : MCHi unit
| IO_read (addr: address_64B_aligned)
  : MCHi (mem (64 Bytes))
| IO_write (addr: address_64B_aligned)
           (val:  mem (64 Bytes))
  : MCHi unit.
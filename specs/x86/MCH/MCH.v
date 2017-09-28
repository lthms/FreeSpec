Require Import FreeSpec.Specs.x86.MCH.SMRAMC.
Require Import FreeSpec.Specs.Memory.
Require Import FreeSpec.Specs.Address.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Undefined.
Require Import FreeSpec.Refine.
Require Import FreeSpec.Compose.
Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Classes.
Require Import FreeSpec.Control.State.
Require Import FreeSpec.Program.
Require Import FreeSpec.WEq.
Require Import FreeSpec.Compose.
Require Import FreeSpec.Specs.Bitfield.
Require Import FreeSpec.Specs.x86.MCH.SMRAMC.
Require Import FreeSpec.Specs.x86.MCH.MemStorage.
Require Import FreeSpec.PropBool.

Local Open Scope free_scope.
Local Open Scope free_prog_scope.
Local Open Scope free_control_scope.

(** * Interface

 *)

Inductive MCHi
  : Interface :=
| PIO_in32 (port:  word)
  : MCHi lword
| PIO_in16 (port:  word)
  : MCHi word
| PIO_in8 (port:  word)
  : MCHi byte
| PIO_out32 (port:  word)
            (val:   lword)
  : MCHi unit
| PIO_out16 (port:  word)
            (val:   word)
  : MCHi unit
| PIO_out8 (port:  word)
            (val:  byte)
  : MCHi unit.

Definition MCHs := unit.

Instance mchs_WEq
  : WEq MCHs :=
  { weq := eq
  }.

(** We need a notation here. If you use a plain ~Definition~, Coq
    cannot find the typeclass instance any longer.

 *)

Definition PCIi := MSi 16.

Definition MCHm
           (A:  Type)
  : Type :=
  StateT MCHs (Program (PCIi <+> Undefined)) A.

(* We have to help a little Coq here. See #16 for more information on
   this matter *)
Definition mch_undefined
           {A: Type}
  : MCHm A :=
  undef (UndefMonad:=undefmonad_Trans _ _).

Definition pci_do
           {A:  Type}
           (i:  PCIi A)
  : MCHm A :=
  '[ileft i].

Definition pio_out8
           (x:  word)
           (v:  byte)
  : MCHm unit :=
  pci_do $ write_byte x v.

Definition pio_out16
           (x:  word)
           (v:  word)
  : MCHm unit :=
  pci_do $ write_word x v.

Definition pio_out32
           (x:  word)
           (v:  lword)
  : MCHm unit :=
  pci_do $ write_lword x v.

Definition pio_in8
           (x:  word)
  : MCHm byte :=
  pci_do $ read_byte x.

Definition pio_in16
           (x:  word)
  : MCHm word :=
   pci_do $ read_word x.

Definition pio_in32
           (x:  word)
  : MCHm lword :=
  pci_do $ read_lword x.

Definition mch_specs
  : StatefulRefinement MCHi (MSi 16 <+> Undefined) MCHs :=
  fun (A: Type)
      (i: MCHi A)
  => match i with
     | PIO_out8 x val
       => pio_out8 x val
     | PIO_out16 x val
       => pio_out16 x val
     | PIO_out32 x val
       => pio_out32 x val
     | PIO_in8 x
       => pio_in8 x
     | PIO_in16 x
       => pio_in16 x
     | PIO_in32 x
       => pio_in32 x
     end.
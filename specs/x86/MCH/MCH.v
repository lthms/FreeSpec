Require Import FreeSpec.Specs.x86.MCH.SMRAMC.
Require Import FreeSpec.Specs.Memory.
Require Import FreeSpec.Specs.Address.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Undefined.
Require Import FreeSpec.Refine.
Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Classes.
Require Import FreeSpec.Control.State.
Require Import FreeSpec.Program.
Require Import FreeSpec.WEq.
Require Import FreeSpec.Compose.

Local Open Scope free_scope.
Local Open Scope free_control_scope.

(** * Interface

 *)

Inductive MCHi
  : Interface :=
| PIO_in32 (port: word)
  : MCHi lword
| PIO_out32 (port: word)
            (val:  lword)
  : MCHi unit
| IO_read (addr: address_64B_aligned)
  : MCHi (mem (64 Bytes))
| IO_write (addr: address_64B_aligned)
           (val:  mem (64 Bytes))
  : MCHi unit.

(** * Hardware Specification

 *)

Inductive ConfAddr
  : Type :=
| confaddr (bus:      nat)
           (device:   nat)
           (function: nat)
           (register: nat)
  : ConfAddr.

Axiom lword_to_confaddr
  : lword -> option ConfAddr.
Axiom confaddr_location
  : word.

Inductive io_write32_target
  : Type :=
| ConfAddr_tar
| Invalid_tar.

Axiom word_to_target
  : word -> option io_write32_target.

Record MCHs :=
  { confAddr: ConfAddr
  }.

Instance mchs_WEq
  : WEq MCHs :=
  { weq := eq
  }.

(** We need a notation here. If you use a plain ~Definition~, Coq
    cannot find the typeclass instance any longer.

 *)
Notation "'MCHm' A":= (StateT MCHs (Program (MCHi <+> Undefined)) A)
                        (at level 30).

(* We have to help a little Coq here. See #16 for more information on
   this matter *)
Definition mch_undefined
           {A: Type}
  : MCHm A :=
  undef (UndefMonad:=undefmonad_Trans _ _).

Definition pio_out32
           (x: word)
           (val: lword)
  : MCHm unit :=
  match word_to_target x with
  | Some ConfAddr_tar
    => pure tt
  | Some _ (* This is a valid target, but it has not been specified
              yet                                                   *)
    => mch_undefined
  | Nothing (* An invalid IO out access is just ignore by the MCH   *)
    => pure tt
  end.

Definition mch_specs
  : StatefulRefinement MCHi (MCHi <+> Undefined) MCHs :=
  fun (A: Type)
      (i: MCHi A)
  => match i with
     | PIO_out32 x val
       => pio_out32 x val
     | _
       => mch_undefined
     end.
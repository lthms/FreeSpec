Require Import FreeSpec.Compose.
Require Import FreeSpec.Specification.
Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Classes.
Require Import FreeSpec.Control.Function.
Require Import FreeSpec.Control.State.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Program.
Require Import FreeSpec.Refine.
Require Import FreeSpec.Specs.Abstract.Abstract.
Require Import FreeSpec.Specs.Abstract.Memory.
Require Import FreeSpec.Specs.Address.
Require Import FreeSpec.Specs.Memory.
Require Import FreeSpec.WEq.

Local Open Scope free_control_scope.
Local Open Scope free_prog_scope.
Local Open Scope free_scope.
Local Open Scope free_weq_scope.

(** * Interface
 *)

Inductive MemoryController_interface
  : Interface :=
| lock_smram
  : MemoryController_interface unit
| toggle_smram
  : MemoryController_interface unit
| read_mc (addr:        address)
          (privileged:  bool)
  : MemoryController_interface byte
| write_mc (addr:        address)
           (privileged:  bool)
           (val:         byte)
  : MemoryController_interface unit.

(** * Implementation

    ** State
 *)

Record MemoryController_state
  : Type :=
  { is_locked:  bool
  ; is_open:    bool
  ; mc_specs:   is_locked = true -> is_open = false
  }.

Program Definition _lock
  : MemoryController_state -> MemoryController_state :=
  pure {| is_locked := true
        ; is_open   := false
        |}.

Program Definition _toggle
        (reg:  MemoryController_state)
  : MemoryController_state :=
  if is_locked reg
  then reg
  else {| is_locked := false
        ; is_open   := negb (is_open reg)
        |}.

Instance MemoryController_state_WEq
  : WEq (MemoryController_state) :=
  { weq := eq
  }.

(** ** Refinement
 *)

Definition DRAM_interface
  : Interface :=
  Memory_interface.

Definition VGA_interface
  : Interface :=
  Memory_interface.

Definition MemoryController_monad
  : Type -> Type :=
  StateT MemoryController_state (Program (DRAM_interface <+> VGA_interface)).

Axiom (in_smram:  address -> bool).

Definition do_dram
           {A:  Type}
           (i:  Memory_interface A)
  : MemoryController_monad A :=
  '[InL i].

Definition do_vga
           {A:  Type}
           (i:  Memory_interface A)
  : MemoryController_monad A :=
  '[InR i].

(* Here we need to explicit MemoryController_monad is an alias to
   StateT. If we don’t, Coq gets lost and says it cannot find an
   instance for MonadState.
 *)
Definition smram_is_locked
  : StateT MemoryController_state (Program (DRAM_interface <+> VGA_interface)) bool :=
  is_locked <$> get.

Definition smram_is_open
  : StateT MemoryController_state (Program (DRAM_interface <+> VGA_interface)) bool :=
  is_open <$> get.

Definition smram_is_unlocked
  : MemoryController_monad bool :=
  negb <$> smram_is_locked.

Definition lock_smramc
  : StateT MemoryController_state (Program (DRAM_interface <+> VGA_interface)) unit :=
  modify _lock.

Definition toggle_smramc
  : StateT MemoryController_state (Program (DRAM_interface <+> VGA_interface)) unit :=
  modify _toggle.

Definition MemoryController_specification
  : StatefulRefinement MemoryController_interface
                       (Memory_interface <+> Memory_interface)
                       MemoryController_state :=
  fun (A:  Type)
      (i:  MemoryController_interface A)
  => match i with
     | lock_smram
       => lock_smramc
     | toggle_smram
       => toggle_smramc
     | read_mc x true
       => do_dram (read_mem x)
     | read_mc x false
       => opn <- smram_is_open                                       ;
          if andb (in_smram x) opn
          then do_dram (read_mem x)
          else do_vga (read_mem x)
     | write_mc x true v
       => do_dram (write_mem x v)
     | write_mc x false v
       => opn <- smram_is_open                                       ;
          if andb (in_smram x) opn
          then do_dram (write_mem x v)
          else do_vga (write_mem x v)
     end.

(** * Specification

    ** Abstract State

    The abstract state is a view on the memory.
 *)

Definition MemoryController_abstract_step
           (A:    Type)
           (i:    MemoryController_interface A)
           (_:    A)
           (map:  Abstract)
  : Abstract :=
  match i with
  | write_mc a true x
    => update a x map
  | _
    => map
  end.

Definition MemoryController_precondition
           (A:    Type)
           (i:    MemoryController_interface A)
           (map:  Abstract)
  : Prop :=
  True.

Definition MemoryController_postcondition
           (A:    Type)
           (i:    MemoryController_interface A)
           (ret:  A)
           (map:  Abstract)
  : Prop :=
  match i
        in MemoryController_interface A'
        return A = A' -> Prop
  with
  | read_mc a true
    => fun (H:  A = byte)
       => eq_rect _ id ret _ H = map a
  | _
    => fun _
       => True
  end (eq_refl A).

Definition MemoryController_specs
  : Specification Abstract MemoryController_interface :=
  {| abstract_step := MemoryController_abstract_step
   ; precondition  := MemoryController_precondition
   ; postcondition := MemoryController_postcondition
   |}.
Require Import FreeSpec.Specs.Memory.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Function.
Require Import FreeSpec.MonadInterp.
Require Import FreeSpec.Control.State.
Require Import FreeSpec.Control.Classes.
Require Import FreeSpec.Control.Identity.
Require Import FreeSpec.WEq.

Local Open Scope free_weq_scope.
Local Open Scope free_control_scope.

Inductive MemStorage_int
          (n:  nat)
  : Interface :=
| read_ms (addr:  mem n)
  : MemStorage_int n byte
| write_ms (addr:  mem n)
           (val:   byte)
  : MemStorage_int n unit.

Arguments read_ms {n} (addr).
Arguments write_ms {n} (addr val).

Definition MemStorage_state
           (n:  nat)
  := mem n
     -> byte.

Definition MemStorage_state_weq
           {n:             nat}
           (store store':  MemStorage_state n)
  : Prop :=
  forall (addr: mem n),
    store addr == store' addr.

Instance MemStorage_state_WEq
         (n:  nat)
  : WEq (MemStorage_state n) :=
  { weq := @MemStorage_state_weq n
  }.

Definition MemStorage_init
           (n:  nat)
  : MemStorage_state n :=
  pure (zero 8).

Definition MemStorage_interp
           {n:  nat}
           {A:  Type}
           (i:  MemStorage_int n A)
  : State (MemStorage_state n) A :=
  match i with
  | read_ms addr
    => gets (fun store => store addr)
  | write_ms addr val
    => modify (fun store addr'
               => if addr ?= addr'
                  then val
                  else store addr')
  end.

Instance memstorage_MonadInterp
         (n:  nat)
  : MonadInterp (MemStorage_int n) (State (MemStorage_state n)) :=
  { interpret := @MemStorage_interp n
  }.
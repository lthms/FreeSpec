Require Import Coq.Program.Program.

Require Import FreeSpec.Specs.Memory.
Require Import FreeSpec.Specs.Bitfield.

Record SMRAMC :=
  { d_lock: bool
  ; d_open: bool
  ; d_cls:  bool
  }.

Definition SMRAMC_bf
  : Bitfield 8 SMRAMC :=
  skip 4                  :;
  d_lck  :<- bit           ;
  d_cls  :<- bit           ;
  d_open :<- bit           ;
  skip 1                  :;

  bf_pure {| d_lock  := d_lck
           ; d_open := d_open
           ; d_cls  := d_cls
           |}.

Definition parse_smramc
           (b: byte)
  : SMRAMC :=
  parse SMRAMC_bf b.
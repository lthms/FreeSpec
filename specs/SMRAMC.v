Require Import FreeSpec.Specs.Memory.
Require Import Coq.Program.Program.
Require Import Omega.

Definition SMRAMC : Type := byte.

Definition SMRAMC_C_BASE_SEG : Type := mem 3.
Definition SMRAMC_D_LCK : Type := mem 1.
Definition SMRAMC_D_CLS : Type := mem 1.
Definition SMRAMC_D_OPEN : Type := mem 1.

Definition read_c_base_seg
           (reg: SMRAMC)
  : SMRAMC_C_BASE_SEG :=
  cast 3 reg.

Program Definition read_d_lck
        (reg: SMRAMC)
  : SMRAMC_D_LCK :=
  cast 1 (shiftr reg 4).

Program Definition read_d_cls
        (reg: SMRAMC)
  : SMRAMC_D_LCK :=
  cast 1 (shiftr reg 5).

Program Definition read_d_open
        (reg: SMRAMC)
  : SMRAMC_D_OPEN :=
  cast 1 (shiftr reg 6).
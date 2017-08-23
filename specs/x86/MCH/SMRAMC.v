Require Import FreeSpec.Specs.Memory.
Require Import Coq.Program.Program.
Require Import Omega.

Definition SMRAMC : Type := byte.

Definition SMRAMC_C_BASE_SEG : Type := mem 3.
Definition SMRAMC_D_LCK : Type := mem 1.
Definition SMRAMC_D_CLS : Type := mem 1.
Definition SMRAMC_D_OPEN : Type := mem 1.

Program Definition read_c_base_seg
        (reg: SMRAMC)
  : SMRAMC_C_BASE_SEG :=
  extract reg 0 3.
Next Obligation.
  apply OpenNat.le_0_n.
Defined.
Next Obligation.
  repeat constructor.
Defined.

Program Definition read_d_lck
        (reg: SMRAMC)
  : SMRAMC_D_LCK :=
  extract reg 4 1.

Program Definition read_d_cls
        (reg: SMRAMC)
  : SMRAMC_D_LCK :=
  extract reg 5 1.

Program Definition read_d_open
        (reg: SMRAMC)
  : SMRAMC_D_OPEN :=
  extract reg 6 1.
Require Import FreeSpec.Libs.Vector.Vector.
Require Import FreeSpec.Specs.Hexa.
Require Import FreeSpec.Specs.Memory.
Require Import Coq.Program.Program.
Require Import Omega.

Definition SMRAMC : Type := byte.

Definition SMRAMC_C_BASE_SEG : Type := mem 3.
Definition SMRAMC_D_LCK : Type := bit.
Definition SMRAMC_D_CLS : Type := bit.
Definition SMRAMC_D_OPEN : Type := bit.

Program Definition read_c_base_seg
        (reg: SMRAMC)
  : { f: SMRAMC_C_BASE_SEG | forall i, i < 3 -> nth f i = nth reg i } :=
  take reg 3.
Next Obligation.
  repeat apply le_n_S.
  assert (forall i, 0 <= i). {
    induction i.
    constructor.
    apply le_S.
    exact IHi.
  }
  apply H.
Defined.

Program Definition read_d_lck
        (reg: SMRAMC)
  : { f: SMRAMC_D_LCK | Some f = nth reg 4 } :=
  head (extract reg 5 4).
Next Obligation.
  destruct head.
  destruct take.
  destruct drop.
  cbn in *.
  rewrite <- e1; [| omega ].
  rewrite <- e0; [| omega].
  symmetry.
  exact e.
Defined.

Program Definition read_d_cls
        (reg: SMRAMC)
  : { f: SMRAMC_D_LCK | Some f = nth reg 5 } :=
  head (extract reg 6 5).
Next Obligation.
  destruct head.
  destruct take.
  destruct drop.
  cbn in *.
  rewrite <- e1; [| omega ].
  rewrite <- e0; [| omega].
  symmetry.
  exact e.
Defined.

Program Definition read_d_open
        (reg: SMRAMC)
  : { f: SMRAMC_D_OPEN | Some f = nth reg 6 } :=
  head (extract reg 7 6).
Next Obligation.
  destruct head.
  destruct take.
  destruct drop.
  cbn in *.
  rewrite <- e1; [| omega ].
  rewrite <- e0; [| omega].
  symmetry.
  exact e.
Defined.
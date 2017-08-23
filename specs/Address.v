Require Import FreeSpec.Specs.Memory.
Require Import Coq.Init.Nat.

(* we only consider 32 bit system *)
Definition address := lword.

Definition is_pow_2
           (n: nat)
  : Prop :=
  2 ^ (Nat.log2 n) = n.

Program Definition is_aligned
        (x:    address)
        (base: nat | is_pow_2 base)
  : Prop :=
  cast base x = box base 0.

Program Definition aligned_address
        (n: nat | is_pow_2 n)
  : Type :=
  {addr: address | is_aligned addr n}.

Program Definition address_64B_aligned
  : Type :=
  aligned_address 64.
Next Obligation.
  reflexivity.
Defined.
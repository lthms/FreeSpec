Require Import FreeSpec.Specs.Memory.
Require Import Coq.Init.Nat.
Require Import Coq.NArith.NArith.

(* we only consider 32 bit system *)
Definition address := lword.

Local Close Scope nat_scope.
Local Open Scope N_scope.

Definition is_pow_2
           (n:  N)
  : Prop :=
  2 ^ (N.log2 n) = n.

Program Definition is_aligned
        (x:     address)
        (base:  N | is_pow_2 base)
  : Prop :=
  cast base x = box base 0.

Program Definition aligned_address
        (n:  N | is_pow_2 n)
  : Type :=
  {addr: address | is_aligned addr n}.

Program Definition address_64B_aligned
  : Type :=
  aligned_address 64.
Next Obligation.
  reflexivity.
Defined.
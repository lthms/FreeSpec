Require Import FreeSpec.Interface.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Contract.
Require Import FreeSpec.WEq.

Local Open Scope free_weq_scope.

Definition reference_contract
           {I:  Interface}
  : Contract (Interp I) I :=
  {| abstract_step := fun (A:  Type)
                          (i:  I A)
                          (_:  A)
                          (s:  Interp I)
                     => execInstruction s i
   ; requirements := fun (A:  Type)
                         (_:  I A)
                         (_: Interp I)
                     => True
   ; promises := fun (A:    Type)
                     (i:    I A)
                     (res:  A)
                     (s:    Interp I)
                 => evalInstruction s i = res
  |}.

Theorem interp_eq_reference_contract
        {I:    Interface}
        (ref:  Interp I)
        (int:  Interp I)
  : int == ref
    -> int :> reference_contract [ref].
Proof.
  revert ref int.
  cofix.
  intros ref int [Hres Hnext].
  constructor.
  + intros A i Htrue.
    cbn.
    symmetry.
    apply Hres.
  + intros A i Htrue.
    cbn.
    apply interp_eq_reference_contract.
    apply Hnext.
Qed.

Corollary reference_compliant_reference_contract
          {I:    Interface}
          (ref:  Interp I)
  : ref :> reference_contract [ref].
Proof.
  apply interp_eq_reference_contract.
  reflexivity.
Qed.
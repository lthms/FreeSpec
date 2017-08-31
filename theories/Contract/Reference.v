Require Import FreeSpec.Interface.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Contract.

Definition reference_contract
           {I:    Interface}
           (int:  Interp I)
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
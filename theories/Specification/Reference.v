Require Import FreeSpec.Interface.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Specification.
Require Import FreeSpec.WEq.

Local Open Scope free_weq_scope.

Definition reference_specification
           {I:  Interface}
  : Specification (Semantics I) I :=
  {| abstract_step := fun (A:  Type)
                          (e:  I A)
                          (_:  A)
                          (s:  Semantics I)
                     => execEffect s e
   ; precondition := fun (A:  Type)
                         (_:  I A)
                         (_: Semantics I)
                     => True
   ; postcondition := fun (A:    Type)
                          (e:    I A)
                          (res:  A)
                          (s:    Semantics I)
                      => evalEffect s e = res
  |}.

Theorem semantics_eq_reference_specification
        {I:    Interface}
        (ref:  Semantics I)
        (sig:  Semantics I)
  : sig == ref
    -> sig |= reference_specification [ref].
Proof.
  revert ref sig.
  cofix.
  intros ref sig [Hres Hnext].
  constructor.
  + intros A e Htrue.
    cbn.
    symmetry.
    apply Hres.
  + intros A e Htrue.
    cbn.
    apply semantics_eq_reference_specification.
    apply Hnext.
Qed.

Corollary reference_compliant_reference_specification
          {I:    Interface}
          (ref:  Semantics I)
  : ref |= reference_specification [ref].
Proof.
  apply semantics_eq_reference_specification.
  reflexivity.
Qed.
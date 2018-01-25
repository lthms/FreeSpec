Require Import Coq.Sets.Ensembles.
Require Import FreeSpec.Specification.
Require Import FreeSpec.Interface.

Inductive NonceGen
          (A:  Type)
  : Interface :=
| gen_nonce
  : NonceGen A A.

Arguments gen_nonce [A].

Module NonceSpecification.
  Definition State
             (A:  Type)
  : Type :=
    Ensemble A.

  Definition gen_nonce_postcondition
             {A:      Type}
             (nonce:  A)
             (set:    State A)
    : Prop :=
    ~ In A set nonce.

  Definition gen_nonce_step
             {A:      Type}
             (nonce:  A)
             (set:    State A)
    : State A :=
    Union A (Singleton A nonce) set.

  Definition specification
             (A:  Type)
    : Specification (State A) (NonceGen A) :=
    {| abstract_step := fun (R:      Type)
                            (i:      NonceGen A R)
                            (x:      R)
                            (state:  State A)
                       => match i, x with
                          | gen_nonce, x
                            => gen_nonce_step x state
                          end
     ; precondition := no_pre
     ; postcondition := fun (R:      Type)
                            (i:      NonceGen A R)
                            (x:      R)
                            (state:  State A)
                        => match i, x with
                           | gen_nonce, x
                             => gen_nonce_postcondition x state
                           end
     |}.
End NonceSpecification.
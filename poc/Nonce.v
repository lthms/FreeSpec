Require Import Coq.Sets.Ensembles.
Require Import FreeSpec.Contract.
Require Import FreeSpec.Interface.

Inductive NonceGen
          (A:  Type)
  : Interface :=
| gen_nonce
  : NonceGen A A.

Arguments gen_nonce [A].

Module NonceContract.
  Definition State
             (A:  Type)
  : Type :=
    Ensemble A.

  Definition gen_nonce_promises
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

  Definition contract
             (A:  Type)
    : Contract (State A) (NonceGen A) :=
    {| abstract_step := fun (R:      Type)
                            (i:      NonceGen A R)
                            (x:      R)
                            (state:  State A)
                       => match i, x with
                          | gen_nonce, x
                            => gen_nonce_step x state
                          end
     ; requirements := no_req
     ; promises := fun (R:      Type)
                       (i:      NonceGen A R)
                       (x:      R)
                       (state:  State A)
                   => match i, x with
                      | gen_nonce, x
                        => gen_nonce_promises x state
                      end
     |}.
End NonceContract.
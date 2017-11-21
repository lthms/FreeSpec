Require Import FreeSpec.Undefined.
Require Import FreeSpec.Contract.
Require Import FreeSpec.Interp.

(** We now define a generic-purpose contract called “escape the
    undefined hell”. From a safety/secure point of view, one should
    avoid the [undef] instruction at all cost, because we cannot
    reason about it.

    The [escape_undefined_hell] is here to verify that.

 *)
Definition escape_undefined_hell_step :=
  fun (R:  Type)
      (_:  Undefined R)
      (_:  R)
      (_:  unit)
  => tt.

Definition escape_undefined_hell_requirements :=
  fun (R:  Type)
      (_:  Undefined R)
      (_:  unit)
  => False.

Definition escape_undefined_hell_promises :=
  fun (R:  Type)
      (_:  Undefined R)
      (_:  R)
      (_:  unit)
  => True.

Definition escape_undefined_hell
  : Contract unit Undefined :=
  {| abstract_step := escape_undefined_hell_step
   ; requirements  := escape_undefined_hell_requirements
   ; promises      := escape_undefined_hell_promises
   |}.

(** It is easy to prove that any [Interp Undefined] [i] complies to
    that contract if the counter is still set to [0], that is: [i :>
    escape_undefined_hell [tt]]

 *)

Lemma escape_undefined_hell_compliance
      (int:  Interp Undefined)
  : int |= escape_undefined_hell [tt].
Proof.
  constructor.
  + intros A i Hreq.
    destruct Hreq.
  + intros A i Hreq.
    destruct Hreq.
Qed.

(** The main idea behing the [escape_undefined_hell] contract is to be
    used as soon as the [Undefined] interface is used in a
    specification.

 *)
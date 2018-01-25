Require Import FreeSpec.Undefined.
Require Import FreeSpec.Specification.
Require Import FreeSpec.Semantics.

(** We now define a generic-purpose specification called “escape the
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

Definition escape_undefined_hell_precondition :=
  fun (R:  Type)
      (_:  Undefined R)
      (_:  unit)
  => False.

Definition escape_undefined_hell_postcondition :=
  fun (R:  Type)
      (_:  Undefined R)
      (_:  R)
      (_:  unit)
  => True.

Definition escape_undefined_hell
  : Specification unit Undefined :=
  {| abstract_step  := escape_undefined_hell_step
   ; precondition   := escape_undefined_hell_precondition
   ; postcondition  := escape_undefined_hell_postcondition
   |}.

(** It is easy to prove that any [Semantics Undefined] [i] complies to
    with specification if the counter is still set to [0], that is: [i
    :> escape_undefined_hell [tt]]

 *)

Lemma escape_undefined_hell_compliance
      (int:  Semantics Undefined)
  : int |= escape_undefined_hell [tt].
Proof.
  constructor.
  + intros A e Hpre.
    destruct Hpre.
  + intros A e Hpre.
    destruct Hpre.
Qed.

(** The main idea behing the [escape_undefined_hell] specification is
    to be used as soon as the [Undefined] interface is used in a
    model.

 *)
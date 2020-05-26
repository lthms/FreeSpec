From FreeSpec.Exec Require Import Exec Eval.

From Coq.Program Require Import Wf.
From Coq Require Import List.
Import ListNotations.

(** [Exec] and the Coq’s Program framework do not always play nicely
    together. The computation of proofs induced by the framework, for instance
    to assert well-founded recursion, can make [Exec] very slow by default. *)

#[program]
Fixpoint enum {a b ix} (p : a -> impure ix b) (l : list a) {measure (length l)} : impure ix unit :=
  match l with
  | nil => pure tt
  | cons x rst => p x;;
                  enum p rst
  end.

Fail Timeout 1 Exec (enum eval [true; true; false]).

(** We have provided an attribute for [Exec] which slightly changes the behavior
    of the command. Note that this is not a silver bullet, as some computations
    may behave just fine with the default behavior, but on the contrary take
    forever to compute with this option enabled. *)

#[nf]
Exec (enum eval [true; true; false]).

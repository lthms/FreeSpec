From FreeSpec Require Import Exec Debug.

From Coq.Program Require Import Wf.
From Coq Require Import List.
Import ListNotations.

#[program]
Fixpoint enum {a b ix} (p : a -> impure ix b) (l : list a) {measure (length l)} : impure ix unit :=
  match l with
  | nil => pure tt
  | cons x rst => do void (p x);
                     enum p rst
                  end
  end.

#[nf] Exec (enum inspect [true; true; false]).

Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Option.
Require Import FreeSpec.PoC.Db.
Require Import FreeSpec.Program.
Require Import FreeSpec.WEq.

Require Import Coq.Strings.String.

Local Open Scope free_weq_scope.

Inductive TransportError
  : Type :=
| transport_error.

Record User :=
  { email:   string
  ; name:    string
  ; token:   option string
  }.

Module UserDbSpec <:  DbSpec.
  Definition K   := nat.
  Definition Res := User.
  Definition Err := TransportError.
End UserDbSpec.

Module Export UserDb := DB UserDbSpec.

Definition head
           {A:  Type}
           (l:  list A)
  : option A :=
  match l with
  | cons x rest
    => Some x
  | nil
    => None
  end.

Definition user_from_email
           (ml:  string)
  : Program Query (option UserDb.Entity) :=
  head <$> DSL.select (fun entity
                       => ml ?= email (val entity)).

Definition user_key_from_email
           (ml:  string)
  : Program Query (option nat) :=
  map key <$> user_from_email ml.
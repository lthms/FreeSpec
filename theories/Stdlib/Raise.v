From FreeSpec.Core Require Import All.

Class Into (α β : Type) :=
  { into : α -> β }.

Instance refl_Into (α : Type) : Into α α :=
  { into := fun x => x }.

Inductive RAISE (α : Type) : interface :=
| Raise {β} (x : α) : RAISE α β.

Arguments Raise [α β] x.

Definition raise `{Into δ α, Provide ix (RAISE α)} {β} (x : δ) : impure ix β :=
  request (Raise (into x)).

Definition try `{Into δ α, Provide ix (RAISE α)} {β} (p : impure ix (δ + β)) : impure ix β :=
  let* res := p in
  match res with
  | inl e => raise e
  | inr x => pure x
  end.

Fixpoint with_raise {ix α β} (p : impure (ix + RAISE α) β) : impure ix (α + β) :=
  match p with
  | local x => local (inr x)
  | request_then (in_right (Raise x)) f => local (inl x)
  | request_then (in_left e) f => request_then e (fun x => with_raise (f x))
  end.

Fixpoint recover {ix α β} (p : impure (ix + RAISE α) β) (h : α -> impure ix β) : impure ix β :=
  let* res := with_raise p in
  match res with
  | inl e => h e
  | inr x => pure x
  end.

Declare Scope raise_scope.

Notation "'recover' p 'with'  v 'of' t '=>' h 'end'" :=
  (recover p (fun (v : t) => h)) : raise_scope.

#[global]
Open Scope raise_scope.

Definition halt_on_error {ix α} (p : impure (ix + RAISE α) unit) : impure ix unit :=
  recover p
  with _ of α => pure tt
  end.

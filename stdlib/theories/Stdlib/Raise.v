From FreeSpec Require Import Core.

Generalizable All Variables.

Class Into (a b : Type) :=
  { into : a -> b
  }.

Instance refl_Into (a : Type) : Into a a :=
  { into := fun x => x
  }.

Inductive RAISE (a : Type) : interface :=
| Raise {b} (x : a) : RAISE a b.

Arguments Raise [a b] x.

Definition raise `{Into c a, Provide ix (RAISE a)} {b} (x : c) : impure ix b :=
  request (Raise (into x)).

Definition try `{Into c a, Provide ix (RAISE a)} {b} (p : impure ix (c + b)) : impure ix b :=
  do var res <- p in
     match res with
     | inl e => raise e
     | inr x => pure x
     end
  end.

Fixpoint recover {ix a b} (p : impure (ix ⊕ RAISE a) b) (h : a -> impure ix b) : impure ix b :=
  match p with
  | local x => local x
  | request_then (in_right (Raise e)) _ => h e
  | request_then (in_left e) f => request_then e (fun x => recover (f x) h)
  end.

Notation "'recover' p 'with'  v 'of' t '=>' h 'end'" := (recover p (fun (v : t) => h)).

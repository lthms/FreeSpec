(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2018–2019 Thomas Letan <thomas.letan@ssi.gouv.fr>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>.
 *)

(** In [FreeSpec.Core.Interface], we have introduced the [interface] type, to
    model the set of primitives an impure computation can use. We also introduce
    [MayProvide], [Provide] and [Distinguish]. They are three type classes which
    allow for manipulating _polymorphic interface composite_.


    In this library, we provide the [impure] monad, defined after the
    <<Program>> monad introduced by the <<operational>> package (see
    <<https://github.com/whitequark/unfork#introduction>>). *)

From Coq Require Import Program Setoid Morphisms.
From Prelude Require Import All.
From FreeSpec.Core Require Import Interface.

#[local]
Open Scope signature_scope.

(** * Impure Computations *)

(** We introduce the [impure] monad to describe impure computations, that is
    computations which uses primitives from certain interfaces. *)

(** ** Definition *)

(** The [impure] monad is an inductive datatype with two parameters: the
    interface [i] to be used, and the type [α] of the result of the computation.
    The fact that [impure] is inductive rather than co-inductive means it is not
    possible to describe infinite computations.  This also means it is possible
    to interpret impure computations within Coq, providing an operational
    semantics for [i]. *)

Inductive impure (i : interface) (α : Type) : Type :=
| local (x : α) : impure i α
| request_then {β} (e : i β) (f : β -> impure i α) : impure i α.

Arguments local [i α] (x).
Arguments request_then [i α β] (e f).

Register impure as freespec.core.impure.type.
Register local as freespec.core.impure.local.
Register request_then as freespec.core.impure.request_then.

(** ** Equivalence *)

(** Due to the definition of [impure] and [impure_bind], we could decide to rely
    on Coq built-in [eq] to reason about impure computations equivalence, but we
    would have to use the functional extensionality axiom to handle the
    continuation of the [request_then] constructor. In order to keep FreeSpec
    axiom-free, we rather provide a custom equivalence for [impure] terms.

    The definition of [impure_equiv] is two-fold. *)

Inductive impure_equiv {i α} : impure i α -> impure i α -> Prop  :=

(** - Two impure computations are equivalent if and only if they compute the
      exact same term (wrt. Coq [eq] function). *)

| local_equiv (x : α) : impure_equiv (local x) (local x)

(** - Two computations which consist in requesting the interpretation of an
      primitive and passing the result to a monadic continuation are equivalent
      if and only if they use the exact same primitive in the first place, and
      given any result the interpretation of this primitive may produce, their
      continuation returns equivalent impure computations. *)

| request_equiv {β} (e : i β) (f g : β -> impure i α)
    (equ : forall (x : β), impure_equiv (f x) (g x))
  : impure_equiv (request_then e f) (request_then e g).

(** The definition of [impure_equiv] is very similar to [eq], with the exception
    of the treatment of the continuation. There is no much effort to put into
    proving this is indeed a proper equivalence. *)

#[program]
Instance impure_equiv_Equivalence : Equivalence (@impure_equiv i α).

Next Obligation.
  intros p.
  induction p; constructor.
  intros x.
  apply H.
Qed.

Next Obligation.
  intros p q equ.
  induction equ; constructor.
  intros x.
  apply H.
Qed.

Next Obligation.
  intros p q r pq qr.
  revert p r pq qr.
  induction q; intros p r pq qr.
  + inversion pq; ssubst; inversion qr; ssubst.
    constructor.
  + inversion pq; ssubst; inversion qr; ssubst.
    constructor.
    intros x.
    now apply H with (β := x).
Qed.

#[program]
Instance impure_Equality : Equality (impure i α).

#[global]
Opaque impure_Equality.

(* FIXME[0]: This works because coq-prelude provides a default [Equality]
   instance for any type is [eq].  Since [b] is universally quantified, there is
   no specific instance to pick expect this one, and therefore the instance of
   Equality for [a -> b] is [forall x, f x = g x], which is exactly what we
   need. *)
#[program]
Instance request_then_Proper : Proper (eq ==> 'equal ==> 'equal) (@request_then i α β).

Next Obligation.
  add_morphism_tactic.
  intros x f g equ.
  now constructor.
Qed.

(** ** Monad Instances *)

(** We then provide the necessary instances of the <<coq-prelude>> Monad
    typeclasses hierarchy. *)

Fixpoint impure_bind {i α β} (p : impure i α) (f : α -> impure i β) : impure i β :=
  match p with
  | local x => f x
  | request_then e g => request_then e (fun x => impure_bind (g x) f)
  end.

#[program]
Instance impure_bind_Proper_1 : Proper (eq ==> 'equal ==> 'equal) (@impure_bind i α β).

Next Obligation.
  add_morphism_tactic.
  intros p f g equf.
  induction p.
  + apply equf.
  + constructor.
    intros sem.
    apply H.
Qed.

#[program]
Instance impure_bind_Proper_2 : Proper ('equal ==> eq ==> 'equal) (@impure_bind i α β).

Next Obligation.
  add_morphism_tactic.
  intros p q equp f.
  induction equp.
  + reflexivity.
  + cbn.
    constructor.
    apply H.
Qed.

Ltac change_request_then :=
  match goal with
  | |- request_then ?e ?f == request_then ?e ?g =>
    let R := fresh "R" in
    assert (R: f == g); [ intros ?x | rewrite R; clear R ]
  end.

Ltac change_impure_bind :=
  match goal with
  | |- impure_bind ?e ?f == impure_bind ?e ?g =>
    let R := fresh "R" in
    assert (R: f == g); [ intros ?x | now rewrite R ]
  end.

Lemma impure_bind_local {i α} (p : impure i α) : impure_bind p (fun x => local x) == p.

Proof.
  induction p.
  + reflexivity.
  + cbn.
    change_request_then; [| reflexivity ].
    now rewrite H.
Qed.

Lemma impure_bind_assoc {i α β δ}
  (p : impure i α) (f : α -> impure i β) (g : β -> impure i δ)
  : impure_bind (impure_bind p f) g == impure_bind p (fun x => impure_bind (f x) g).

Proof.
  induction p; [reflexivity |].
  cbn.
  change_request_then; [| reflexivity ].
  now rewrite H.
Qed.

(* see FIXME[0] *)
Definition impure_map {i α β} (f : α -> β) (p : impure i α) : impure i β :=
  impure_bind p (fun x => local (f x)).

#[program]
Instance impure_map_Proper : Proper ('equal ==> 'equal ==> 'equal) (@impure_map i α β).

Next Obligation.
  add_morphism_tactic.
  intros f g equf p q equp.
  unfold impure_map.
  rewrite equp.
  change_impure_bind.
  now rewrite equf.
Qed.

#[program]
Instance impure_Functor : Functor (impure i) :=
  { map := @impure_map i
  }.

Next Obligation.
  unfold impure_map.
  now rewrite impure_bind_local.
Defined.

Next Obligation.
  unfold compose.
  unfold impure_map.
  now rewrite impure_bind_assoc.
Defined.

Definition impure_pure {i α} (x : α) : impure i α := local x.

Definition impure_apply {i α β} (p : impure i (α -> β)) (q : impure i α) : impure i β :=
  impure_bind p (fun f => map f q).

#[program]
Instance impure_apply_Proper : Proper ('equal ==> 'equal ==> 'equal) (@impure_apply i α β).

Next Obligation.
  add_morphism_tactic.
  intros p q equ1 r s equ2.
  unfold impure_apply.
  rewrite equ1.
  change_impure_bind.
  cbn.
  now rewrite equ2.
Qed.

#[program, universes(polymorphic)]
Instance impure_Applicative : Applicative (impure i) :=
  { pure := @impure_pure i
  ; apply := @impure_apply i
  }.

Next Obligation.
  unfold impure_apply, impure_pure, impure_bind.
  now rewrite functor_identity.
Defined.

Next Obligation.
  unfold impure_apply, impure_pure; cbn.
  unfold impure_map.
  repeat rewrite impure_bind_assoc.
  change_impure_bind; cbn.
  repeat rewrite impure_bind_assoc.
  change_impure_bind; cbn.
  repeat rewrite impure_bind_assoc.
  now change_impure_bind.
Defined.

Next Obligation.
  reflexivity.
Qed.

Next Obligation.
  reflexivity.
Qed.

Next Obligation.
  reflexivity.
Qed.

#[program]
Instance impure_Monad (i : interface) : Monad (impure i) :=
  { bind := @impure_bind i
  }.

Next Obligation.
  reflexivity.
Defined.

Next Obligation.
  now rewrite impure_bind_local.
Defined.

Next Obligation.
  now rewrite impure_bind_assoc.
Defined.

Next Obligation.
  now change_impure_bind.
Defined.

Next Obligation.
  reflexivity.
Defined.

(** ** Defining Impure Computations *)

(** FreeSpec users shall not use the [impure] monad constructors directly.  The
    [pure] function from the [Applicative] typeclass allows for defining pure
    computations which do not depend on any impure primitive.  The [bind]
    function from the [Monad] typeclass allows for seamlessly combine impure
    computations together.

    To complete these two monadic operations, we introduce the [request]
    function, whose purpose is to define an impure computation that uses a given
    primitive [e] from an interface [i], and returns its result.  [request] does
    not parameterize the [impure] monad with [i] directly, but rather with a
    generic interface [ix].  [ix] is constrained with the [Provide] notation, so
    that it has to provide at least [i]'s primitives.  *)

Definition request `{ix :| i} {α} (e : i α) : impure ix α :=
  request_then (inj_p e) (fun* x => pure x).

(** Note: there have been attempts to turn [request] into a typeclass
    function (to seamlessly use [request] with a [MonadTrans] instance such as
    [state_t]). The reason why it has not been kept into the codebase is that
    the flexibility it gives for writing code has a real impact on the
    verification process. It is simpler to reason about “pure” impure
    computations (that is, not within a monad stack), then wrapping these
    computations thanks to [lift].

    The <<coq-prelude>> provides notations (inspired by the do notation of
    Haskell) to write monadic functions more easily.  These notations live
    inside the [monad_scope]. *)

Declare Scope impure_scope.
Bind Scope monad_scope with impure.

Instance store_monad_state (s : Type) (ix : interface) `{ix :| STORE s}
  : MonadState s (impure ix) :=
  { put := fun (x : s) => request (Put x)
  ; get := request Get
  }.

(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2018–2019 Thomas Letan <thomas.letan@ssi.gouv.fr>
 *
 * This impure is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This impure is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>.
 *)

(** In this library, we provide all the necessary concepts to model interacting
    components using Coq.  We do that by means of a variant of the Free monad
    introduced by the Haskell ~operational~ package, and originally called the
    Program monad thereafter.  The Program monad is parameterized by a type
    which describes the interfaces its monadic computations can use, where an
    interface describes a set of functions carried out by an outer environment
    expected to produce a result.  In other words, using the ~operational~
    Program monad, we model impurity.

    To avoid ambiguity with the Program framework of Coq, we rename the Program
    monad the [impure] monad, and we call “impure computations” the monadic
    computations which happens within the [impure] monad.  We call “primitives”
    the impure functions provided by a given interface.

    The key idea behind FreeSpec is to model components as functions which maps
    primitives of the interface it exposes to impure computations parameterized
    by the interfaces it uses. *)

From Coq.Program Require Import Equality Tactics Basics.
From Coq Require Import Morphisms.
From Coq Require Import Relations Setoid Morphisms.
From Prelude Require Import Equality Control Control.Classes Tactics State.
From FreeSpec.Core Require Import utils.

#[local]
Open Scope signature_scope.

#[local]
Open Scope prelude_scope.

Notation "''equal'" := (@equal _ _) (only parsing).

(** * Interfaces *)

(** Following the definition of the ~operational~ package, interfaces in
    FreeSpec are parameterized inductive types whose terms purposely describe
    the primitives the interface provides. *)

Definition interface := Type -> Type.

(** Given [i : interface], a term of type [i α] identifies a primitive of [i]
    expected to produce a result of type [α].

    The simpler interface is the empty interface, which provides no primitives
    whatsoever. *)

Inductive iempty : interface := .
Notation "'<>'" := iempty : type_scope.
Notation "'⋄'" := iempty : type_scope.

(** To use the [⋄] interface to parameterize the [impure] monad is equivalent to
    writing pure functions.

    Another example of general-purpose interface we can define is the [STORE s]
    interface, where [s] is a type, and [STORE s] allows for manipulating a
    global, mutable variable of type [s] within an impure computation.

<<
Inductive STORE (s : Type) : interface :=
| Get : STORE s s
| Put (x : s) : STORE s unit.
>>

    According to the definition of [STORE s], an impure computation can use two
    primitives. The term [Get : STORE s s] describes a primitive expected to
    produce a result of type [s], that is the current value of the mutable
    variable.  Terms of the form [Put x : STORE s unit] describe a primitive
    which does not produce any meaningful result, but is expected to update the
    current value of the mutable variable.

    The use of the word “expected” to describe the primitive of [STORE s] is
    voluntary.  The definition of a semantics does not attach any particular
    semantics to the primitives it describes.  This will come latter, and in
    fact, one interface may have many legitimate semantics.

    Impure computations are likely to use more than one interface, but the
    [impure] monad takes only one argument.  We introduce [iplus] (denoted by
    [<+>] or [⊕]) to compose interfaces together.  An impure computation
    parameterized by [i ⊕ j] can therefore leverages the privimites of both [i]
    and [j]. *)


Inductive iplus (i j : interface) (a : Type) :=
| in_left (e : i a) : iplus i j a
| in_right (e : j a) : iplus i j a.

Arguments in_left [i j a] (e).
Arguments in_right [i j a] (e).

Infix "<+>" := iplus (at level 50, left associativity) : type_scope.
Infix "⊕" := iplus (at level 50, left associativity) : type_scope.

(** When defining general-purpose impure computations that we expect to reuse in
    different context, we want to leave the interface as a parameter, and rather
    express the constrains in terms of interface availability.  To do that, we
    introduce the [Provide] typeclass, such that [Provide ix i] implies impure
    computations parameterized by [ix] can use primitives of [i]. *)

Class Provide (ix i : interface) : Type :=
  { lift_eff {a : Type} (e : i a) : ix a
  }.

#[program]
Instance refl_Provide (i : interface) : Provide i i :=
  { lift_eff := fun (a : Type) (e : i a) => e
  }.

#[program]
Instance iplus_left_Provide (i j : interface) : Provide (i ⊕ j) i :=
  { lift_eff := @in_left i j
  }.

#[program]
Instance iplus_right_Provide (i j : interface) : Provide (i ⊕ j) j :=
  { lift_eff := @in_right i j
  }.

(** We introduce a dedicated notation for conveniently declare interface
    requirements.  Our main source of inspiration is the PureScript row of
    effects.

    Afterwards, we can write [`{ix :| INTERFACE1, INTERFACE2}] to say that [ix]
    provides at least [INTERFACE1] and [INTERFACE2] primitives. *)

Notation "ix ':|' i1 ',' i2 ',' .. ',' i3" :=
  (CCons (Provide ix i1) (CCons (Provide ix i2) .. (CCons (Provide ix i3) CNil) ..))
    (at level 78, i1, i2, i3 at next level, no associativity)
  : type_scope.

Notation "ix ':|' i" :=
  (Provide ix i)
    (at level 78, i at next level, no associativity)
  : type_scope.

(* begin hide *)
#[local]
Definition provide_notation_test_1 {a}
  (ix i1 i2 i3 : interface) `{ix :| i1, i2, i3} (p : i2 a) : ix a :=
  lift_eff p.

#[local]
Definition provide_notation_test_2 {a}
  (ix i1 i2 i3 : interface) `{ix :| i1, i2, i3} (p : forall i' `{ix :| i2, i3}, i' a)
  : ix a :=
  p ix.
(* end hide *)

(** * Operational Semantics *)

(** We have already explained interfaces, in FreeSpec, does not attach any
    particular semantics to their primitives.  Once an interface has been
    defined, we can provide one (or more) operational semantics to interpret its
    primitives. *)

(** ** Definition *)

(** An operational [semantics] for the interface [i] is coinductively defined as
    a function which can be used to interpret any primitive of [i]; it produces
    an [interp_out] terms. *)

CoInductive semantics (i : interface) : Type :=
| mk_semantics (f : forall (a : Type), i a -> interp_out i a) : semantics i

(** A term of type [interp_out i a] is therefore the result of the
    interpretation of a given primitive [i a]. It provides a result for this
    primitive (of type [a]), and the new semantics to use to interpret the next
    primitive of [i]. *)

with interp_out (i : interface) : Type -> Type :=
| mk_out {a} (x : a) (sem : semantics i) : interp_out i a.

(** Thus, a [semantics] does not only compute a result for a primitive, but also
    provides a new semantics.  This is necessary to model impurity: the same
    primitive may or may not return the same result when called several
    times. *)

Arguments mk_semantics [i] (f).
Arguments mk_out [i a] (x sem).

(** As for interfaces, the simpler [semantics] is the operational semantics for
    [⋄], the empty interface. *)

Definition semempty : semantics ⋄ :=
  mk_semantics (fun (a : Type) (e : iempty a) => match e with end).

(** As an example, we provide a semantics for the [STORE s] interface:

<<
CoFixpoint store {s} (init : s) : semantics (STORE s) :=
  mk_semantics (fun (a : Type) (e : STORE s a) =>
                  match e with
                  | Get => mk_out init (store init)
                  | Put next => mk_out tt (store next)
                  end).
>> *)

(** We provide several helper functions to interpret primitives with
    semantics. *)

Definition run_effect {i a} (sem : semantics i) (e : i a) : interp_out i a :=
  match sem with mk_semantics f => f _ e end.

Definition interp_result {i a} (step : interp_out i a) : a :=
  match step with mk_out x _ => x end.

Definition interp_next {i a} (step : interp_out i a) : semantics i :=
  match step with mk_out _ sem => sem end.

Definition eval_effect {i a} (sem : semantics i) (e : i a) : a :=
  interp_result (run_effect sem e).

Definition exec_effect {i a} (sem : semantics i) (e : i a) : semantics i :=
  interp_next (run_effect sem e).

(** Besides, and similarly to interfaces, operational semantics can and should
    be composed together.  To that end, we provide the [semplus] operation
    (denoted by [<+>] or [⊕]). *)

CoFixpoint semplus {i j} (sem_i : semantics i) (sem_j : semantics j)
  : semantics (i ⊕ j) :=
  mk_semantics (fun (a : Type) (e : (i ⊕ j) a) =>
                  match e with
                  | in_left e =>
                    let out := run_effect sem_i e in
                    mk_out (interp_result out) (semplus (interp_next out) sem_j)
                  | in_right e =>
                    let out := run_effect sem_j e in
                    mk_out (interp_result out) (semplus sem_i (interp_next out))
                  end).

Infix "<x>" := semplus (at level 50, left associativity) : semantics_scope.
Infix "⊗" := semplus (at level 50, left associativity) : semantics_scope.

Bind Scope semantics_scope with semantics.

(** ** Equivalence *)

(** We say two semantics are equivalent when (1) we they produce equivalent outputs
    given the same primitive. *)

CoInductive semantics_equiv {i} : semantics i -> semantics i -> Prop :=
| semantics_equiv_rec
    (sem sem' : semantics i)
    (step_equiv : forall {a} (e : i a),
        interp_out_equiv (run_effect sem e) (run_effect sem' e))       (* (1) *)
  : semantics_equiv sem sem'

(** Two interpretation output are said equivalent when (1) they carry the same
    result, and they provide equivalent semantics to use afterwards. *)

with interp_out_equiv {i} : forall {a : Type}, interp_out i a -> interp_out i a -> Prop :=
| step_equiv {a}
    (o o' : interp_out i a)
    (res_eq : interp_result o = interp_result o')                      (* (1) *)
    (next_equiv : semantics_equiv (interp_next o) (interp_next o'))    (* (2) *)
  : interp_out_equiv o o'.

(** We prove [semantics_equiv] is an equivalence, that is the relation is (1)
    reflexive, (2) symmetric, and (3) transitive. *)

#[program]
Instance semantics_equiv_Equivalence (i : interface) : Equivalence (@semantics_equiv i).

Obligation 1.
  cofix semantics_equiv_refl.
  intros sem.
  constructor.
  intros a e.
  constructor; [ reflexivity |].
  apply semantics_equiv_refl.
Qed.

Obligation 2.
  cofix semantics_equiv_sym.
  intros sem sem' equiv.
  destruct equiv as [sem sem' step].
  constructor.
  intros a e.
  specialize step with a e.
  destruct step.
  constructor.
  + now symmetry.
  + now apply semantics_equiv_sym.
Qed.

Obligation 3.
  cofix semantics_equiv_trans.
  intros sem sem' sem'' equiv equiv'.
  destruct equiv as [sem sem' equ].
  destruct equiv' as [sem' sem'' equ'].
  constructor; intros a e.
  specialize equ with a e.
  specialize equ' with a e.
  inversion equ; ssubst.
  inversion equ'; ssubst.
  constructor.
  + now transitivity (eval_effect sem' e).
  + eapply semantics_equiv_trans; [ apply next_equiv | apply next_equiv0 ].
Qed.

(** We use [semantics_equiv] as the [Equality] relation for [semantics]. *)

#[program]
Instance semantics_Equality (i : interface) : Equality (semantics i).

#[global]
Opaque semantics_Equality.

(** We proceed similarly with [interp_out_equiv]: we first prove it is an
    equivalence, then we use this relation as the [Equality] relation for
    [interp_out]. *)

#[program]
Instance interp_out_Equivalence (i : interface) (a : Type)
  : Equivalence (@interp_out_equiv i a).

Obligation 1.
  intros [x sem].
  constructor; reflexivity.
Qed.

Obligation 2.
  intros o o' equ.
  inversion equ; ssubst.
  now constructor.
Qed.

Obligation 3.
  intros o o' o'' equ equ'.
  inversion equ; ssubst.
  inversion equ'; ssubst.
  constructor.
  + now transitivity (interp_result o').
  + now transitivity (interp_next o').
Qed.

#[program]
Instance interp_out_Equality (i : interface) (a : Type) : Equality (interp_out i a).

#[global]
Opaque interp_out_Equality.

(** Since [interp_out_equiv] and [semantics_equiv] are two equivalence, we can
    use them with the [rewrite] tactics, as long as we provide valid [Proper]
    instances.  We proceed accordingly in FreeSpec.Core, as systematically as
    possible. *)

#[program]
Instance mk_out_Proper (i : interface) (a : Type)
  : Proper (eq ==> 'equal ==> 'equal) (@mk_out i a).

Next Obligation.
  add_morphism_tactic.
  intros x sem sem' equ.
  constructor.
  + reflexivity.
  + apply equ.
Qed.

#[program]
Instance run_effect_Proper (i : interface) (a : Type)
  : Proper ('equal ==> eq ==> 'equal) (@run_effect i a).

Next Obligation.
  add_morphism_tactic.
  intros sem sem' equ p.
  inversion equ; ssubst.
  apply step_equiv0.
Qed.

#[program]
Instance interp_result_Proper (i : interface) (a : Type)
  : Proper ('equal ==> eq) (@interp_result i a).

Next Obligation.
  add_morphism_tactic.
  intros o o' equ.
  now inversion equ; ssubst.
Qed.

#[program]
Instance interp_next_Proper (i : interface) (a : Type)
  : Proper ('equal ==> 'equal) (@interp_next i a).

Next Obligation.
  add_morphism_tactic.
  intros o o' equ.
  now inversion equ; ssubst.
Qed.

#[program]
Instance eval_effect_Proper (i : interface) (a : Type)
  : Proper ('equal ==> eq ==> eq) (@eval_effect i a).

Next Obligation.
  add_morphism_tactic.
  intros o o' equ e.
  unfold eval_effect.
  now rewrite equ.
Qed.

#[program]
Instance exec_effect_Proper (i : interface) (a : Type)
  : Proper ('equal ==> eq ==> 'equal) (@exec_effect i a).

Next Obligation.
  add_morphism_tactic.
  intros o o' equ e.
  unfold exec_effect.
  now rewrite equ.
Qed.

Lemma semantics_equiv_interp_next_effect {i a}
  (sem sem' : semantics i) (equ : sem == sem') (e : i a)
  : interp_next (run_effect sem e) == interp_next (run_effect sem' e).
Proof.
  inversion equ; ssubst.
  specialize step_equiv0 with a e.
  inversion step_equiv0; ssubst.
  apply next_equiv.
Qed.

Hint Resolve semantics_equiv_interp_next_effect : freespec.

Lemma semantics_equiv_exec_effect {i a}
  (sem sem' : semantics i) (equ : sem == sem') (e : i a)
  : exec_effect sem e == exec_effect sem' e.
Proof.
  unfold exec_effect.
  auto with freespec.
Qed.

Hint Resolve semantics_equiv_exec_effect : freespec.

#[program]
Instance semplus_Proper (i j : interface)
  : Proper ('equal ==> 'equal ==> 'equal) (@semplus i j).

Next Obligation.
  add_morphism_tactic.
  cofix semplus_Proper.
  intros semi semi' equi semj semj' equj.
  constructor.
  intros a e.
  destruct e; constructor; cbn.
  + now rewrite equi.
  + apply semplus_Proper; auto with freespec.
  + now rewrite equj.
  + apply semplus_Proper; auto with freespec.
Qed.

(** * Impure Computations *)

(** We introduce the [impure] monad to describe impure computations, that is
    computations which uses primitives from certain interfaces.

    ** Definition

    The [impure] monad is an inductive datatype with two parameters: the
    interface [i] to be used, and the type [a] of the result of the computation.
    The fact that [impure] is inductive rather than co-inductive means it is not
    possible to describte infinite computations.  This also means it is possible
    to interpret impure computation within Coq, providing an operational
    semantics for [i]. *)

Inductive impure (i : interface) (a : Type) : Type :=
| local (x : a) : impure i a
| request_then {b} (e : i b) (f : b -> impure i a) : impure i a.

Arguments local [i a] (x).
Arguments request_then [i a b] (e f).

(** ** Equivalence *)

Inductive impure_equiv {i a} : impure i a -> impure i a -> Prop  :=
| local_equiv (x : a) : impure_equiv (local x) (local x)
| request_equiv {b} (e : i b) (f g : b -> impure i a)
    (equ : forall (x : b), impure_equiv (f x) (g x))
  : impure_equiv (request_then e f) (request_then e g).

#[program]
Instance impure_equiv_Equivalence (i : interface) (a : Type)
  : Equivalence (@impure_equiv i a).

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
    now apply H with (b := x).
Qed.

#[program]
Instance impure_Equality (i : interface) (a : Type) : Equality (impure i a).

#[global]
Opaque impure_Equality.

(** ** Monad Instances *)

(* FIXME[0]: This works because coq-prelude provides a default [Equality]
   instance for any type is [eq].  Since [b] is universally quantified, there is
   no specific instance to pick expect this one, and therefore the instance of
   Equality for [a -> b] is [forall x, f x = g x], which is exactly what we
   need. *)
#[program]
Instance request_then_Proper (i : interface) (a b : Type)
  : Proper (eq ==> 'equal ==> 'equal) (@request_then i a b).

Next Obligation.
  add_morphism_tactic.
  intros x f g equ.
  now constructor.
Qed.

Fixpoint impure_bind {i a b} (p : impure i a) (f : a -> impure i b) : impure i b :=
  match p with
  | local x => f x
  | request_then e g => request_then e (fun x => impure_bind (g x) f)
  end.

#[program]
Instance impure_bind_Proper_1 (i : interface) (a b : Type)
  : Proper (eq ==> 'equal ==> 'equal) (@impure_bind i a b).

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
Instance impure_bind_Proper_2 (i : interface) (a b : Type)
  : Proper ('equal ==> eq ==> 'equal) (@impure_bind i a b).

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

Lemma impure_bind_local {i a} (p : impure i a) : impure_bind p (@local i a) == p.
Proof.
  induction p.
  + reflexivity.
  + cbn.
    change_request_then; [| reflexivity ].
    now rewrite H.
Qed.

Lemma impure_bind_assoc {i a b c}
  (p : impure i a) (f : a -> impure i b) (g : b -> impure i c)
  : impure_bind (impure_bind p f) g == impure_bind p (fun x => impure_bind (f x) g).
Proof.
  induction p; [reflexivity |].
  cbn.
  change_request_then; [| reflexivity ].
  now rewrite H.
Qed.

(* see FIXME[0] *)
Definition impure_map {i a b} (f : a -> b) (p : impure i a) : impure i b :=
  impure_bind p (fun x => local (f x)).

#[program]
Instance impure_map_Proper (i : interface) (a b : Type)
  : Proper ('equal ==> 'equal ==> 'equal) (@impure_map i a b).

Next Obligation.
  add_morphism_tactic.
  intros f g equf p q equp.
  unfold impure_map.
  rewrite equp.
  change_impure_bind.
  now rewrite equf.
Qed.

#[program]
Instance impure_Functor (i : interface) : Functor (impure i) :=
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

Definition impure_pure {i a} : a -> impure i a :=
  @local i a.

Definition impure_apply {i a b} (p : impure i (a -> b)) (q : impure i a) : impure i b :=
  impure_bind p (fun f => map f q).

#[program]
Instance impure_apply_Proper (i : interface) (a b : Type)
  : Proper ('equal ==> 'equal ==> 'equal) (@impure_apply i a b).

Next Obligation.
  add_morphism_tactic.
  intros p q equ1 r s equ2.
  unfold impure_apply.
  rewrite equ1.
  change_impure_bind.
  cbn.
  now rewrite equ2.
Qed.

#[program, polymorphic]
Instance impure_Applicative (i : interface) : Applicative (impure i) :=
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

    To complete these two monadic operation, we introduce the [request]
    function, whose purpose is to define an impure computation that uses a given
    primitive [e] from an interface [i], and returns its result.  [request] does
    not parameterize the [impure] monad with [i] directly, but rather with a
    generic interface [ix].  [ix] is constrained with the [Provide] notation, so
    that it has to provide at least [i]'s primitives.  *)

Definition request {ix i} `{ix :| i} {a : Type} (e : i a) : impure ix a :=
  request_then (lift_eff e) (fun x => local x).

(** The ~coq-prelude~ provides notations (inspired by the do notation of
    Haskell) to write monadic functions more easily.  These notations live
    inside the [monad_scope] scope. *)

Bind Scope monad_scope with impure.

(** ** Interpreting Impure Computations *)

Fixpoint run_impure {i a} (sem : semantics i) (p : impure i a) : interp_out i a :=
  match p with
  | local x =>
    mk_out x sem
  | request_then e f =>
    let s := run_effect sem e in
    run_impure (interp_next s) (f (interp_result s))
  end.

Definition eval_impure {i a} (sem : semantics i) (p : impure i a) : a :=
  interp_result (run_impure sem p).

Definition exec_impure {i a} (sem : semantics i) (p : impure i a) : semantics i :=
  interp_next (run_impure sem p).

Lemma run_impure_request_then_equ {i a b} (sem : semantics i)
  (e : i a) (f : a -> impure i b)
  : run_impure sem (request_then e f) = run_impure (exec_effect sem e) (f (eval_effect sem e)).
Proof eq_refl.

Hint Rewrite @run_impure_request_then_equ : freespec.

Lemma semantics_equiv_interp_next_impure {i a}
  (sem sem' : semantics i) (equ : sem == sem') (p : impure i a)
  : interp_next (run_impure sem p) == interp_next (run_impure sem' p).
Proof.
  revert sem sem' equ.
  induction p; intros sem sem' equ.
  + apply equ.
  + cbn.
    unfold exec_impure.
    cbn.
    rewrite equ at 2.
    apply H.
    auto with freespec.
Qed.

Hint Resolve semantics_equiv_interp_next_impure : freespec.

Lemma semantics_equiv_exec_impure {i a}
  (sem sem' : semantics i) (equ : sem == sem') (p : impure i a)
  : exec_impure sem p == exec_impure sem' p.
Proof.
  unfold exec_impure.
  auto with freespec.
Qed.

Hint Resolve semantics_equiv_exec_impure : freespec.

#[program]
Instance run_impure_Proper_1 (i : interface) (a : Type)
  : Proper ('equal ==> eq ==> 'equal) (@run_impure i a).

Next Obligation.
  add_morphism_tactic.
  intros sem sem' equ p.
  revert sem sem' equ.
  induction p; intros sem sem' equ.
  + cbn.
    now rewrite equ.
  + cbn.
    rewrite equ at 2.
    auto with freespec.
Qed.

#[program]
Instance run_impure_Proper_2 (i : interface) (a : Type)
  : Proper (eq ==> 'equal ==> 'equal) (@run_impure i a).

Next Obligation.
  add_morphism_tactic.
  intros sem p q equ.
  revert sem.
  induction equ; intros sem.
  + reflexivity.
  + apply H.
Qed.

#[program]
Instance eval_impure_Proper (i : interface) (a : Type)
  : Proper ('equal ==> 'equal ==> eq) (@eval_impure i a).

Next Obligation.
  add_morphism_tactic.
  intros sem sem' equ1 p q equ2.
  unfold eval_impure.
  now rewrite equ1, equ2.
Qed.

#[program]
Instance exec_impure_Proper (i : interface) (a : Type)
  : Proper ('equal ==> 'equal ==> 'equal) (@exec_impure i a).

Next Obligation.
  add_morphism_tactic.
  intros sem sem' equ1 p q equ2.
  unfold exec_impure.
  now rewrite equ1, equ2.
Qed.

Lemma run_impure_equiv {i a} (p q : impure i a) (equ : p == q) (sem : semantics i)
  : run_impure sem p == run_impure sem q.
Proof.
  now rewrite equ.
Qed.

Hint Resolve run_impure_equiv : freespec.

Lemma run_impure_exec_impure_equiv {i a}
  (sem sem' : semantics i) (p q : impure i a) (equ : run_impure sem p == run_impure sem' q)
  : exec_impure sem p == exec_impure sem' q.
Proof.
  now inversion equ; ssubst.
Qed.

Hint Resolve run_impure_exec_impure_equiv : freespec.

Lemma run_impure_eval_impure_equiv {i a}
  (sem sem' : semantics i) (p q : impure i a) (equ : run_impure sem p == run_impure sem' q)
  : eval_impure sem p = eval_impure sem' q.
Proof.
  now inversion equ; ssubst.
Qed.

Hint Resolve run_impure_eval_impure_equiv : freespec.

Lemma exec_impure_equiv {i a} (p q : impure i a) (equ : p == q) (sem : semantics i)
  : exec_impure sem p == exec_impure sem q.
Proof.
  now rewrite equ.
Qed.

Hint Resolve run_impure_equiv : freespec.

Lemma impure_bind_equation {i a b}
  (p : impure i a) (f : a -> impure i b) (sem : semantics i)
  : run_impure sem (impure_bind p f)
    == run_impure (exec_impure sem p) (f (eval_impure sem p)).
Proof.
  revert sem.
  induction p; intros sem.
  + reflexivity.
  + cbn.
    apply H.
Qed.

(** * Component

    In FreeSpec, we call a component an entity which exposes an interface [i],
    and uses primitives of an interface [j] to compute the result of primitives
    of [i].  Besides, a component is likely to carry its own internal state (of
    type [s]).

<<
                               c : component i j s
                           i +---------------------+      j
                           | |                     |      |
                   +------>| |       st : s        |----->|
                           | |                     |      |
                             +---------------------+
>>

    Thus, a component [c : component i j s] is a polymorphic function which,
    given a primitive of [i], and the current state of the component, maps
    impure computations which return the result of the primitive and the new
    state of the component.  We use the State monad [state_t] to handle the
    internal state of the component more easily.  We could have use the [STORE
    s] interface discussed previously, but we believe using [state_t] simplifies
    the reasoning process of FreeSpec. *)

Definition component (i j : interface) (s : Type) : Type :=
  forall (a : Type), i a -> state_t s (impure j) a.


(** The similarity between FreeSpec components and operational semantics may be
    confusing at first.  The main difference between the two concepts is simple:
    operational semantics are self-contained terms which can, alone, be used to
    interpret impure computations of a given interface.  Components, on the
    other hand, are not self-contained.  Without an intial state [init : s] and
    an operational semantics for [j], we cannot use a component [c : component i
    j s] to interpret an impure computation using [i].

    Given an initial state and and initial semantics for [j], we can however
    derive an operational semantics for [i] from a component [c]. *)

CoFixpoint derive_semantics {i j s} (c : component i j s) (st : s) (sem : semantics j) :=
  mk_semantics (fun (a : Type) (e : i a) =>
                  let out := run_impure sem (c a e st) in
                  let res := interp_result out in
                  let sem' := interp_next out in
                  mk_out (fst res) (derive_semantics c (snd res) sem')).

(** So, [⊕] on the onde hand allows for composing operational semantics
    horizontally, and [derive_semantics] allows for composing components
    vertically.  Using these two operators, we can model a complete system in a
    modular manner, by defining each of its component independently, then
    composing them together with [⊕] and [derive_semantics]. *)

Definition bootstrap {i s} (c : component i ⋄ s) (st : s) :=
  derive_semantics c st semempty.

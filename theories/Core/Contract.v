(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2018–2020 Thomas Letan <thomas.letan@ssi.gouv.fr>
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

(** In this library, we provide the necessary material to reason about FreeSpec
    components both in isolation, and in composition.  To do that, we focus our
    reasoning principles on interfaces, by defining how their primitives shall
    be used, and what to expect the result computed by “correct” operational
    semantics (according to a certain definition of “correct”). *)

From Coq Require Import Setoid Morphisms.
From ExtLib Require Import StateMonad MonadState MonadTrans.
From FreeSpec.Core Require Import Interface Impure Semantics Component.

#[local]
Open Scope signature_scope.

(** * Definition *)

(** A contract dedicated to [i : interface] primarily provides two
    predicates.

    - [caller_obligation] distinguishes between primitives that can be used (by
      an impure computation), and primitives that cannot be used.
    - [callee_obligation] specifies which guarantees can be expected from
      primitives results, as computed by a “good” operational semantics.

    Both [caller_obligation] and [callee_obligation] model properties that may
    vary in time, e.g., a primitive may be forbidden at a given time, but
    authorized later.  To take this possibility into account, contracts are
    parameterized by what we have called a “witness.”  A witness is a term which
    describes the necessary information of the past, and allows for taking
    decision for the present.  It can be seen as an abstraction of the concrete
    state of the interface implementor.

    To keep this state up-to-date after each primitive interpretation,
    contracts also define a dedicated function [witness_update]. *)

Record contract (i : interface) (Ω : Type) : Type := make_contract
  { witness_update (ω : Ω) : forall (α : Type), i α -> α -> Ω
  ; caller_obligation (ω : Ω) : forall (α : Type),  i α -> Prop
  ; callee_obligation (ω : Ω) : forall (α : Type), i α -> α -> Prop
  }.

Declare Scope contract_scope.
Bind Scope contract_scope with contract.

Arguments make_contract [i Ω] (_ _ _).
Arguments witness_update [i Ω] (c ω) [α] (_ _).
Arguments caller_obligation [i Ω] (c ω) [α] (_).
Arguments callee_obligation [i Ω] (c ω) [α] (_ _).

(** The most simple contract we can define is the one that requires
    anything both for the impure computations which uses the primitives of a
    given interface, and for the operational semantics which compute results for
    these primitives. *)

Definition const_witness {i} :=
  fun (u : unit) (α : Type) (e : i α) (x : α) => u.

Inductive no_caller_obligation {i Ω} (ω : Ω) (α : Type) (e : i α) : Prop :=
| mk_no_caller_obligation : no_caller_obligation ω α e.

Hint Constructors no_caller_obligation : freespec.

Inductive no_callee_obligation {i Ω} (ω : Ω) (α : Type) (e : i α) (x : α) : Prop :=
| mk_no_callee_obligation : no_callee_obligation ω α e x.

Hint Constructors no_callee_obligation : freespec.

Definition no_contract (i : interface) : contract i unit :=
  {| witness_update := const_witness
   ; caller_obligation := no_caller_obligation
   ; callee_obligation := no_callee_obligation
   |}.

(** A similar —and as simple— contract is the one that forbids the use of a
    given interface. *)

Definition do_no_use {i Ω} (ω : Ω) (α : Type) (e : i α) : Prop := False.

Definition forbid_specs (i : interface) : contract i unit :=
  {| witness_update := const_witness
   ; caller_obligation := do_no_use
   ; callee_obligation := no_callee_obligation
   |}.

(** * Composing Contracts *)

(** As we compose interfaces and operational semantics, we can easily compose
    contracts together, by means of the [cplus] operator. Given [i] and [j]
    two interfaces, if we can reason about [i] and [j] independently (e.g., the
    caller obligations of [j] do not vary when we use [i]), then we can compose
    [ci : contract i Ωi] and [cj : contract j Ωj], such that [cplus ci cj] in a
    contract for [i + j]. *)

Definition gen_witness_update `{MayProvide ix i} {Ω α} (c : contract i Ω)
    (ω :  Ω) (e : ix α) (x : α)
  : Ω :=
  match proj_p e with
  | Some e => witness_update c ω e x
  | None => ω
  end.

Definition gen_caller_obligation `{MayProvide ix i} {Ω α} (c : contract i Ω)
    (ω :  Ω) (e : ix α)
  : Prop :=
  match proj_p e with
  | Some e => caller_obligation c ω e
  | None => True
  end.

Definition gen_callee_obligation `{MayProvide ix i} {Ω α} (c : contract i Ω)
    (ω :  Ω) (e : ix α) (x : α)
  : Prop :=
  match proj_p e with
  | Some e => callee_obligation c ω e x
  | None => True
  end.

Definition cplus `{Provide ix i, Provide ix j} {Ωi Ωj}
    (ci : contract i Ωi) (cj : contract j Ωj)
  : contract ix (Ωi * Ωj) :=
  {| witness_update := fun (ω : Ωi * Ωj) (α : Type) (e : ix α) (x : α) =>
                         (gen_witness_update ci (fst ω) e x, gen_witness_update cj (snd ω) e x)
  ;  caller_obligation := fun (ω : Ωi * Ωj) (α : Type) (e : ix α) =>
                       gen_caller_obligation ci (fst ω) e /\ gen_caller_obligation cj (snd ω) e
  ;  callee_obligation := fun (ω : Ωi * Ωj) (α : Type) (e : ix α) (x : α) =>
                   gen_callee_obligation ci (fst ω) e x /\ gen_callee_obligation cj (snd ω) e x
  |}.

Infix "+" := cplus : contract_scope.

(** Finally, and as an example, we define a contract for the interface
    [STORE s] we discuss in [FreeSpec.Core.Impure].  As a reminder, the
    interface is defined as follows:

<<
Inductive STORE (s : Type) : interface :=
| Get : STORE s s
| Put (x : s) : STORE s unit.
>>

    For [STORE s], the best witness is the actual value of the mutable
    variable.  Therefore, the contract for [STORE s] may be [specs (STORE
    s) s], and the witness will be updated after each [Put] call. *)

Definition store_update (s : Type) :=
  fun (x : s) (α : Type) (e : STORE s α) (_ : α) =>
    match e with
    | Get => x
    | Put x' => x'
    end.

(** Assuming the mutable variable is being initialized prior to any impure
    computation interpretation, we do not have any obligations over the use of
    [STORE s] primitives.  We will get back to this assertion once we have
    defined our contract, but in the meantime, we define its callee obligation.

    The logic of these callee obligations is as follows: [Get] is expected to
    produce a result strictly eqv to the witness, and we do not have any
    obligations about the result of [Put] (which belongs to [unit] anyway, so
    there is not much to tell). *)

Inductive o_callee_store (s : Type) (x : s) : forall (α : Type), STORE s α -> α -> Prop :=
| get_o_callee (x' : s) (equ : x = x') : o_callee_store s x s Get x'
| put_o_callee (x' : s) (u : unit) : o_callee_store s x unit (Put x') u.

(** The actual contract can therefore be defined as follows: *)

Definition store_specs (s : Type) : contract (STORE s) s :=
  {| witness_update := store_update s
  ;  caller_obligation := no_caller_obligation
  ;  callee_obligation := o_callee_store s
  |}.

(** Now, as we briefly mentionned, this contract allows for reasoning about an
    impure computation which uses the [STORE s] interface, assuming the mutable,
    global variable has been initialized.  We can define another contract that
    does not rely on such assumption, and on the contrary, requires an impure
    computation to initialize the variable prior to using it.

    In this context, the witness can solely be a boolean which tells if the
    variable has been initialized, and the [callee_obligation] will require the
    witness to be [true] to authorize a call of [Get].

    This is one of the key benefits of the FreeSpec approach: because the
    contracts are defined independently from impure computations and
    interfaces, we can actually define several contracts to consider
    different set of hypotheses. *)

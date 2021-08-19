(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

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

#[global] Hint Constructors no_caller_obligation : freespec.

Inductive no_callee_obligation {i Ω} (ω : Ω) (α : Type) (e : i α) (x : α) : Prop :=
| mk_no_callee_obligation : no_callee_obligation ω α e x.

#[global] Hint Constructors no_callee_obligation : freespec.

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

(** * Contract Equivalence *)

Definition contract_caller_impl `(c1 : contract i Ω1) `(c2 : contract i Ω2)
    (iso : Ω1 -> Ω2 -> Prop)
  : Prop :=
  forall ω1 ω2 a (p : i a),
    iso ω1 ω2
    -> caller_obligation c1 ω1 p -> caller_obligation c2 ω2 p.

Definition contract_callee_impl `(c1 : contract i Ω1) `(c2 : contract i Ω2)
    (iso : Ω1 -> Ω2 -> Prop)
  : Prop :=
  forall ω1 ω2 a (p : i a) x,
    iso ω1 ω2
    -> callee_obligation c1 ω1 p x -> callee_obligation c2 ω2 p x.

Definition contract_witness_impl `(c1 : contract i Ω1) `(c2 : contract i Ω2)
    (iso : Ω1 -> Ω2 -> Prop)
  : Prop :=
  forall ω1 ω2 a (p : i a) x,
    iso ω1 ω2
    -> iso (witness_update c1 ω1 p x) (witness_update c2 ω2 p x).

Inductive contract_impl `(c1 : contract i Ω1) `(c2 : contract i Ω2)
  : Type :=
| mk_contract_impl (iso : Ω1 -> Ω2 -> Prop)
    (caller_impl : contract_caller_impl c1 c2 iso)
    (callee_impl : contract_callee_impl c2 c1 (fun ω2 ω1 => iso ω1 ω2))
    (witness_impl : contract_witness_impl c1 c2 iso)
  : contract_impl c1 c2.

Definition ciso `(c1 : contract i Ω1) `(c2 : contract i Ω2)
    (equ : contract_impl c1 c2)
  : Ω1 -> Ω2 -> Prop :=
  match equ with
  | @mk_contract_impl _ _ _ _ _ iso _ _ _ => iso
  end.

Arguments ciso {i Ω1 c1 Ω2 c2} (equ ω1 ω2).

Inductive contract_strong_impl `(c1 : contract i Ω1) `(c2 : contract i Ω2)
  : Type :=
| mk_contract_strong_impl (impl : contract_impl c1 c2)
    (callee_strong_impl : contract_callee_impl c1 c2 (ciso impl))
  : contract_strong_impl c1 c2.

Inductive contract_equ `(c1 : contract i Ω1) `(c2 : contract i Ω2)
  : Type :=
| mk_contract_equ (impl1 : contract_impl c1 c2)
    (impl2 : contract_impl c2 c1)
    (iso_equ : forall ω1 ω2, ciso impl1 ω1 ω2 <-> ciso impl2 ω2 ω1)
  : contract_equ c1 c2.

Infix ">-" := contract_impl (at level 70, no associativity) : freespec_scope.
Infix ">>-" := contract_strong_impl (at level 70, no associativity) : freespec_scope.
Infix "~~" := contract_equ (at level 70, no associativity) : freespec_scope.

#[local] Open Scope freespec_scope.

Definition impl_of_equ `(c1 : contract i Ω1) `(c2 : contract i Ω2)
    (equ : c1 ~~ c2)
  : c1 >- c2.

Proof.
  now induction equ.
Defined.

Definition impl_of_strong_impl `(c1 : contract i Ω1) `(c2 : contract i Ω2)
    (equ : c1 >>- c2)
  : c1 >- c2.

Proof.
  now induction equ.
Defined.

Coercion impl_of_equ : contract_equ >-> contract_impl.
Coercion impl_of_strong_impl : contract_strong_impl >-> contract_impl.

Lemma contract_impl_refl `(c : contract i Ω) : c >- c.

Proof.
  apply mk_contract_impl with (iso:=eq); auto.
  + intros ω1 ω2 α p equ.
    now rewrite equ.
  + intros ω1 ω2 α p x equ.
    now rewrite equ.
  + intros ω1 ω2 α p x equ.
    now rewrite equ.
Defined.

Lemma contract_strong_impl_refl `(c : contract i Ω) : c >>- c.

Proof.
  apply mk_contract_strong_impl with (impl:=contract_impl_refl c); auto.
  intros ω1 ω2 a p x iso.
  cbn in iso.
  now rewrite iso.
Defined.

Lemma contract_equ_refl `(c : contract i Ω)
  : c ~~ c.

Proof.
  now apply (mk_contract_equ c c (contract_impl_refl c) (contract_impl_refl c)).
Defined.

Lemma contract_equ_sym `(c1 : contract i Ω1) `(c2 : contract i Ω2)
    (equ : c1 ~~ c2)
  : contract_equ c2 c1.

Proof.
  inversion equ.
  now apply (mk_contract_equ c2 c1 impl2 impl1).
Defined.

Lemma contract_impl_trans `(c1 : contract i Ω1) `(c2 : contract i Ω2)
   `(c3 : contract i Ω3)
    (impl12 : c1 >- c2) (impl23 : c2 >- c3)
  : c1 >- c3.

Proof.
  destruct impl12 as [iso12 caller_impl12 callee_impl12 witness_impl12].
  destruct impl23 as [iso23 caller_impl23 callee_impl23 witness_impl23].
  apply mk_contract_impl with (iso:=fun ω1 ω3 => exists ω2, iso12 ω1 ω2 /\ iso23 ω2 ω3).
  + intros ω1 ω3 a p [ω2 [is_iso12 is_iso23]] ocaller.
    apply caller_impl23 with (ω1:=ω2); auto.
    apply caller_impl12 with (ω1:=ω1); auto.
  + intros ω3 ω1 a p x [ω2 [is_iso12 is_iso23]] ocaller.
    apply (callee_impl12 ω2 ω1); auto.
    apply (callee_impl23 ω3 ω2); auto.
  + intros ω1 ω3 a p x [ω2 [is_iso12 is_iso23]].
    exists (witness_update c2 ω2 p x).
    now split; [ apply witness_impl12 | apply witness_impl23 ].
Defined.

Lemma contract_strong_impl_trans `(c1 : contract i Ω1) `(c2 : contract i Ω2)
   `(c3 : contract i Ω3)
    (simpl12 : c1 >>- c2) (simpl23 : c2 >>- c3)
  : c1 >>- c3.

Proof.
  apply mk_contract_strong_impl
    with (impl:=contract_impl_trans c1 c2 c3 simpl12 simpl23); auto.
  intros ω1 ω2 a p x iso.
  induction simpl12.
  induction simpl23.
  induction impl.
  induction impl0.
  cbn in *.
  rename ω2 into ω3.
  destruct iso as [ω2 [is_iso is_iso']].
  intros ocallee.
  apply (callee_strong_impl0 ω2 ω3); auto.
  apply (callee_strong_impl ω1 ω2); auto.
Defined.

Lemma contract_equ_trans `(c1 : contract i Ω1) `(c2 : contract i Ω2)
   `(c3 : contract i Ω3)
    (equ12 : c1 ~~ c2) (equ23 : c2 ~~ c3)
  : c1 ~~ c3.

Proof.
  inversion equ12; inversion equ23.
  apply (mk_contract_equ
           c1 c3
           (contract_impl_trans c1 c2 c3 impl1 impl0)
           (contract_impl_trans c3 c2 c1 impl3 impl2)).
  intros ω1 ω3.
  induction impl1; induction impl0; induction impl3; induction impl2.
  cbn in *.
  split.
  + intros [ω2 [is_iso1 is_iso2]].
    exists ω2.
    split.
    ++ now rewrite <- iso_equ0.
    ++ now rewrite <- iso_equ.
  + intros [ω2 [is_iso1 is_iso2]].
    exists ω2.
    split.
    ++ now rewrite iso_equ.
    ++ now rewrite iso_equ0.
Qed.

Lemma contract_strong_impl_of_equ `(c1 : contract i Ω1) `(c2 : contract i Ω2)
    (equ : c1 ~~ c2)
  : c1 >>- c2.

Proof.
  induction equ.
  apply mk_contract_strong_impl with (impl:=impl1).
  induction impl2.
  cbn in *.
  intros ω1 ω2 a p x.
  rewrite iso_equ.
  apply (callee_impl ω1 ω2).
Qed.

(** * Composing Contracts *)

(** As we compose interfaces and operational semantics, we can easily compose
    contracts together, by means of the [contractprod] operator. Given [i] and [j]
    two interfaces, if we can reason about [i] and [j] independently (e.g., the
    caller obligations of [j] do not vary when we use [i]), then we can compose
    [ci : contract i Ωi] and [cj : contract j Ωj], such that [contractprod ci cj] in a
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

Definition contractprod `{Provide ix i, Provide ix j} {Ωi Ωj}
    (ci : contract i Ωi) (cj : contract j Ωj)
  : contract ix (Ωi * Ωj) :=
  {| witness_update := fun (ω : Ωi * Ωj) (α : Type) (e : ix α) (x : α) =>
                         (gen_witness_update ci (fst ω) e x, gen_witness_update cj (snd ω) e x)
  ;  caller_obligation := fun (ω : Ωi * Ωj) (α : Type) (e : ix α) =>
                       gen_caller_obligation ci (fst ω) e /\ gen_caller_obligation cj (snd ω) e
  ;  callee_obligation := fun (ω : Ωi * Ωj) (α : Type) (e : ix α) (x : α) =>
                   gen_callee_obligation ci (fst ω) e x /\ gen_callee_obligation cj (snd ω) e x
  |}.

Infix "*" := contractprod : contract_scope.

(** We also introduce a second composition operator which shares the
    witness state among its two operands. *)

Definition sharedcontractprod `{StrictProvide2 ix i j}
   `(ci : contract i Ω) (cj : contract j Ω)
  : contract ix Ω :=
  {|
  witness_update :=
    fun (ω : Ω) (α : Type) (e : ix α) (x : α) =>
      (* we need to check [j] before [i] because [sharedcontractprod]
         will be left associative *)
      match proj_p (i:=j) e with
      | Some e => witness_update cj ω e x
      | _ => match proj_p (i:=i) e with
             | Some e => witness_update ci ω e x
             | _ => ω
             end
      end;
  caller_obligation :=
    fun (ω : Ω) (α : Type) (e : ix α) =>
      gen_caller_obligation ci ω e /\ gen_caller_obligation cj ω e;
  callee_obligation :=
    fun (ω : Ω) (α : Type) (e : ix α) (x : α) =>
      gen_callee_obligation ci ω e x /\ gen_callee_obligation cj ω e x
  |}.

Infix "^" := sharedcontractprod : contract_scope.

(** * Contract By Example *)

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
    produce a result strictly equivalent to the witness, and we do not have any
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

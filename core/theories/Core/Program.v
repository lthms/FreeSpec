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

From Coq.Program Require Import Equality Tactics Basics.
From Coq Require Import Relations Setoid FunctionalExtensionality.
From Prelude Require Import Equality Control Control.Classes Tactics State.

#[local]
Open Scope prelude_scope.
#[local]
Open Scope monad_scope.

Notation "''equal'" := (@equal _ _) (only parsing).

From FreeSpec.Core Require Import utils.

(** * Interfaces *)

Definition interface := Type -> Type.

Inductive iempty : interface := .

Notation "'<>'" := iempty : type_scope.
Notation "'⋄'" := iempty : type_scope.

Inductive iplus (i j : interface) : interface :=
| in_left {a} (e : i a) : iplus i j a
| in_right {a} (e : j a) : iplus i j a.

Arguments in_left [i j a] (e).
Arguments in_right [i j a] (e).

Infix "<+>" := iplus (at level 50, left associativity) : type_scope.
Infix "⊕" := iplus (at level 50, left associativity) : type_scope.

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

Ltac find_use_instance :=
  match goal with
  | H: context[CCons (Provide ?ix ?i) _] |- Provide ?ix ?i =>
    apply H
  end.

Hint Extern 10 (Provide ?ix ?i) => find_use_instance : typeclass_instances.

Notation "ix ':|' i1 ',' i2 ',' .. ',' i3" :=
  (CCons (Provide ix i1) (CCons (Provide ix i2) .. (CCons (Provide ix i3) CNil) ..))
    (at level 78, i1, i2, i3 at next level, no associativity)
  : type_scope.

Notation "ix ':|' i" :=
  (Provide ix i)
    (at level 78, i at next level, no associativity)
  : type_scope.

(** * Operational Semantics *)

CoInductive semantics (i : interface) : Type :=
| mk_semantics : (forall (a : Type), i a -> interp_out i a) -> semantics i
with interp_out (i : interface) : Type -> Type :=
| mk_out {a} (x : a) (sem : semantics i) : interp_out i a.

Arguments mk_semantics [i] (f).
Arguments mk_out [i a] (x sem).

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

CoInductive semantics_equiv {i} : semantics i -> semantics i -> Prop :=
| semantics_equiv_rec
    (** Let [sem] and [sem'] be two operational semantics for [i], if... *)
    (sem sem' : semantics i)
    (** ... given the same effect, they compute equivalent steps... *)
    (step_equiv : forall {a} (e : i a), interp_out_equiv (run_effect sem e)
                                                          (run_effect sem' e))
    (** ... then [sem] and [sem'] are equivalent. *)
  : semantics_equiv sem sem'
with interp_out_equiv {i} : forall {a : Type}, interp_out i a -> interp_out i a -> Prop :=
| step_equiv {a}
    (o o' : interp_out i a)
    (res_eq : interp_result o = interp_result o')
    (next_equiv : semantics_equiv (interp_next o) (interp_next o'))
  : interp_out_equiv o o'.

#[program]
Instance semantics_equiv_Equivalence (i : interface) : Equivalence (@semantics_equiv i).

Next Obligation.
  cofix semantics_equiv_refl.
  intros sem.
  constructor.
  intros a e.
  constructor; [ reflexivity |].
  apply semantics_equiv_refl.
Qed.

Next Obligation.
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

Next Obligation.
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

#[program]
Instance semantics_Equality (i : interface) : Equality (semantics i).
Opaque semantics_Equality.

#[program]
Instance interp_out_Equivalence (i : interface) (a : Type) : Equivalence (@interp_out_equiv i a).

Next Obligation.
  intros [x sem].
  constructor; reflexivity.
Qed.

Next Obligation.
  intros o o' equ.
  inversion equ; ssubst.
  now constructor.
Qed.

Next Obligation.
  intros o o' o'' equ equ'.
  inversion equ; ssubst.
  inversion equ'; ssubst.
  constructor.
  + now transitivity (interp_result o').
  + now transitivity (interp_next o').
Qed.

#[program]
Instance interp_out_Equality (i : interface) (a : Type) : Equality (interp_out i a).
Opaque interp_out_Equality.

#[local]
Open Scope signature_scope.
From Coq Require Import Morphisms.

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

Lemma lm_semantics_equiv_interp_next_effect {i a}
(** Let two equivalent semantics [sem] and [sem'] and an effect [e]... *)
  (sem sem' : semantics i) (equ : sem == sem') (e : i a)
(** ... then the semantics resulting in the interpretation of [e] are
    equivalent. *)
  : interp_next (run_effect sem e) == interp_next (run_effect sem' e).
Proof.
  inversion equ; ssubst.
  specialize step_equiv0 with a e.
  inversion step_equiv0; ssubst.
  apply next_equiv.
Qed.

Hint Resolve lm_semantics_equiv_interp_next_effect : freespec.

Lemma lm_semantics_equiv_exec_effect {i a}
(** Let two equivalent semantics [sem] and [sem'] and an effect [e]... *)
  (sem sem' : semantics i) (equ : sem == sem') (e : i a)
(** ... then [exec_effect sem e] and [exec_effect sem' e] are equivalent. *)
  : exec_effect sem e == exec_effect sem' e.
Proof.
  unfold exec_effect.
  auto with freespec.
Qed.

Hint Resolve lm_semantics_equiv_exec_effect : freespec.

CoFixpoint semempty : semantics ⋄ :=
  mk_semantics (fun (a : Type) (e : iempty a) => match e with end).

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
Infix "⊗" := iplus (at level 50, left associativity) : semantics_scope.

Bind Scope semantics_scope with semantics.

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

(** * Program Monad *)

Inductive program (i : interface) (a : Type) : Type :=
| local (x : a) : program i a
| request_then {b} (e : i b) (f : b -> program i a) : program i a.

Bind Scope monad_scope with program.

Arguments local [i a] (x).
Arguments request_then [i a b] (e f).

Definition request {ix i} `{ix :| i} {a : Type} (e : i a) : program ix a :=
  request_then (lift_eff e) (fun x => local x).

Fixpoint run_program {i a} (sem : semantics i) (p : program i a) : interp_out i a :=
  match p with
  | local x =>
    mk_out x sem
  | request_then e f =>
    let s := run_effect sem e in
    run_program (interp_next s) (f (interp_result s))
  end.

Definition eval_program {i a} (sem : semantics i) (p : program i a) : a :=
  interp_result (run_program sem p).

Definition exec_program {i a} (sem : semantics i) (p : program i a) : semantics i :=
  interp_next (run_program sem p).

(** Let [p] and [q] be two programs which both use effects of the interface [i]
    and produces a result of type [a]… *)
Inductive program_equiv {i a} (p q : program i a) : Prop :=
(** if they _always_ produce the same output, independently from the operational
    semantics… *)
| program_equiv_out (run_equiv : forall (sem : semantics i),
                        run_program sem p == run_program sem q)
(** … then [p] and [q] are said to be equivalent. *)
  : program_equiv p q.

#[program]
Instance program_equiv_Equivalence (i : interface) (a : Type)
  : Equivalence (@program_equiv i a).

Next Obligation.
  intros p.
  constructor.
  reflexivity.
Qed.

Next Obligation.
  intros p q.
  constructor.
  intros sem.
  symmetry.
  apply H.
Qed.

Next Obligation.
  intros p q r pq qr.
  constructor.
  intros sem.
  transitivity (run_program sem q).
  + apply pq.
  + apply qr.
Qed.

#[program]
Instance program_Equality (i : interface) (a : Type) : Equality (program i a).
Opaque program_Equality.

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
  constructor.
  intros sem; cbn.
  specialize equ with (interp_result (run_effect sem x)).
  inversion equ; ssubst.
  apply run_equiv.
Qed.

Lemma lm_semantics_equiv_interp_next_program {i a}
(** Let two equivalent semantics [sem] and [sem'] and a program with effects [p]... *)
  (sem sem' : semantics i) (equ : sem == sem') (p : program i a)
(** ... then the semantics resulting in the interpretation of [p] are
    equivalent. *)
  : interp_next (run_program sem p) == interp_next (run_program sem' p).
Proof.
  revert sem sem' equ.
  induction p; intros sem sem' equ.
  + apply equ.
  + cbn.
    unfold exec_program.
    cbn.
    assert (R: interp_result (run_effect sem e) = interp_result (run_effect sem' e));
      [now rewrite equ | rewrite R; clear R].
    apply H.
    auto with freespec.
Qed.

Hint Resolve lm_semantics_equiv_interp_next_program : freespec.

Lemma lm_semantics_equiv_exec_program {i a}
(** Let two equivalent semantics [sem] and [sem'] and a program with effects [p]... *)
  (sem sem' : semantics i) (equ : sem == sem') (p : program i a)
(** ... then [exec_program sem p] and [exec_program sem' p] are equivalent. *)
  : exec_program sem p == exec_program sem' p.
Proof.
  unfold exec_program.
  auto with freespec.
Qed.

Hint Resolve lm_semantics_equiv_exec_program : freespec.

#[program]
Instance run_program_Proper_1 (i : interface) (a : Type)
  : Proper ('equal ==> eq ==> 'equal) (@run_program i a).

Next Obligation.
  add_morphism_tactic.
  intros sem sem' equ p.
  revert sem sem' equ.
  induction p; intros sem sem' equ.
  + cbn.
    now rewrite equ.
  + cbn.
    assert (R: interp_result (run_effect sem e) = interp_result (run_effect sem' e));
      [| rewrite R; clear R].
    inversion equ; ssubst.
    specialize step_equiv0 with b e.
    now inversion step_equiv0; ssubst.
    apply H.
    auto with freespec.
Qed.

#[program]
Instance run_program_Proper_2 (i : interface) (a : Type)
  : Proper (eq ==> 'equal ==> 'equal) (@run_program i a).

Next Obligation.
  add_morphism_tactic.
  intros sem p q equ.
  apply equ.
Qed.

#[program]
Instance eval_Program_Proper (i : interface) (a : Type)
  : Proper ('equal ==> 'equal ==> eq) (@eval_program i a).

Next Obligation.
  add_morphism_tactic.
  intros sem sem' equ1 p q equ2.
  unfold eval_program.
  now rewrite equ1, equ2.
Qed.

#[program]
Instance exec_Program_Proper (i : interface) (a : Type)
  : Proper ('equal ==> 'equal ==> 'equal) (@exec_program i a).

Next Obligation.
  add_morphism_tactic.
  intros sem sem' equ1 p q equ2.
  unfold exec_program.
  now rewrite equ1, equ2.
Qed.

Fixpoint program_bind {i a b} (p : program i a) (f : a -> program i b) : program i b :=
  match p with
  | local x => f x
  | request_then e g => request_then e (fun x => program_bind (g x) f)
  end.

#[program]
Instance program_bind_Proper_1 (i : interface) (a b : Type)
  : Proper (eq ==> 'equal ==> 'equal) (@program_bind i a b).

Next Obligation.
  add_morphism_tactic.
  intros p f g equf.
  induction p.
  + apply equf.
  + constructor.
    intros sem.
    apply H.
Qed.

Lemma lm_run_program_equiv {i a} (p q : program i a) (equ : p == q) (sem : semantics i)
  : run_program sem p == run_program sem q.
Proof.
  inversion equ.
  apply run_equiv.
Qed.

Hint Resolve lm_run_program_equiv : freespec.

Lemma lm_run_program_exec_program_equiv {i a}
  (sem sem' : semantics i) (p q : program i a) (equ : run_program sem p == run_program sem' q)
  : exec_program sem p == exec_program sem' q.
Proof.
  now inversion equ; ssubst.
Qed.

Hint Resolve lm_run_program_exec_program_equiv : freespec.

Lemma lm_run_program_eval_program_equiv {i a}
  (sem sem' : semantics i) (p q : program i a) (equ : run_program sem p == run_program sem' q)
  : eval_program sem p = eval_program sem' q.
Proof.
  now inversion equ; ssubst.
Qed.

Hint Resolve lm_run_program_eval_program_equiv : freespec.

Lemma lm_exec_program_equiv {i a} (p q : program i a) (equ : p == q) (sem : semantics i)
  : exec_program sem p == exec_program sem q.
Proof.
  inversion equ.
  specialize run_equiv with sem.
  auto with freespec.
Qed.

Hint Resolve lm_run_program_equiv : freespec.

Lemma lm_program_bind_equation {i a b}
  (p : program i a) (f : a -> program i b) (sem : semantics i)
  : run_program sem (program_bind p f) == run_program (exec_program sem p) (f (eval_program sem p)).
Proof.
  revert sem.
  induction p; intros sem.
  + reflexivity.
  + cbn.
    apply H.
Qed.

#[program]
Instance program_bind_Proper_2 (i : interface) (a b : Type)
  : Proper ('equal ==> eq ==> 'equal) (@program_bind i a b).

Next Obligation.
  add_morphism_tactic.
  intros p q equp f.
  constructor.
  intros sem.
  repeat rewrite lm_program_bind_equation.
  assert (R: exec_program sem p == exec_program sem q) by auto with freespec;
    [ rewrite R; clear R ].
  assert (R: eval_program sem p = eval_program sem q) by auto with freespec;
    [ rewrite R; clear R ].
  reflexivity.
Qed.

Ltac change_request_then :=
  match goal with
  | |- request_then ?e ?f == request_then ?e ?g =>
    let R := fresh "R" in
    assert (R: f == g); [ intros ?x | rewrite R; clear R ]
  end.

Ltac change_program_bind :=
  match goal with
  | |- program_bind ?e ?f == program_bind ?e ?g =>
    let R := fresh "R" in
    assert (R: f == g); [ intros ?x | now rewrite R ]
  end.

Lemma lm_program_bind_local {i a} (p : program i a) : program_bind p (@local i a) == p.
Proof.
  induction p.
  + reflexivity.
  + cbn.
    change_request_then; [| reflexivity ].
    now rewrite H.
Qed.

Lemma lm_program_bind_assoc {i a b c}
  (p : program i a) (f : a -> program i b) (g : b -> program i c)
  : program_bind (program_bind p f) g == program_bind p (fun x => program_bind (f x) g).
Proof.
  induction p; [reflexivity |].
  cbn.
  change_request_then; [| reflexivity ].
  now rewrite H.
Qed.

#[local] Open Scope prelude_scope.

(* see FIXME[0] *)
Definition program_map {i a b} (f : a -> b) (p : program i a) : program i b :=
  program_bind p (fun x => local (f x)).

#[program]
Instance program_map_Proper (i : interface) (a b : Type)
  : Proper ('equal ==> 'equal ==> 'equal) (@program_map i a b).

Next Obligation.
  add_morphism_tactic.
  intros f g equf p q equp.
  unfold program_map.
  rewrite equp.
  change_program_bind.
  constructor.
  intros sem.
  cbn.
  constructor.
  + apply equf.
  + reflexivity.
Qed.

#[program]
Instance program_Functor (i : interface) : Functor (program i) :=
  { map := @program_map i
  }.

(** [program_map id x = id x] *)
Next Obligation.
  unfold program_map.
  now rewrite lm_program_bind_local.
Defined.

(** [program_map (v >>> u) x = (program_map v >>> program_map u) x] *)
Next Obligation.
  unfold compose.
  unfold program_map.
  now rewrite lm_program_bind_assoc.
Defined.

Definition program_pure {i a} : a -> program i a :=
  @local i a.

Definition program_apply {i a b} (p : program i (a -> b)) (q : program i a) : program i b :=
  program_bind p (fun f => f <$> q).

#[program]
Instance program_apply_Proper (i : interface) (a b : Type)
  : Proper ('equal ==> 'equal ==> 'equal) (@program_apply i a b).

Next Obligation.
  add_morphism_tactic.
  intros p q equ1 r s equ2.
  unfold program_apply.
  rewrite equ1.
  change_program_bind.
  cbn.
  now rewrite equ2.
Qed.

#[program, polymorphic]
Instance program_Applicative (i : interface) : Applicative (program i) :=
  { pure := @program_pure i
  ; apply := @program_apply i
  }.

(** [program_apply (program_pure id) v = v] *)
Next Obligation.
  unfold program_apply, program_pure, program_bind.
  now rewrite functor_identity.
Defined.

(** [program_apply (program_apply (program_apply (program_pure compose) u) v) w
    = program_apply u (program_apply v w)] *)
Next Obligation.
  unfold program_apply, program_pure; cbn.
  unfold program_map.
  repeat rewrite lm_program_bind_assoc.
  change_program_bind; cbn.
  repeat rewrite lm_program_bind_assoc.
  change_program_bind; cbn.
  repeat rewrite lm_program_bind_assoc.
  now change_program_bind.
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
Instance program_Monad (i : interface) : Monad (program i) :=
  { bind := @program_bind i
  }.

Next Obligation.
  reflexivity.
Defined.

Next Obligation.
  now rewrite lm_program_bind_local.
Defined.

Next Obligation.
  now rewrite lm_program_bind_assoc.
Defined.

Next Obligation.
  now change_program_bind.
Defined.

Next Obligation.
  reflexivity.
Defined.

(** * Component *)

Definition component (i j : interface) (s : Type) : Type :=
  forall (a : Type), i a -> state_t s (program j) a.

CoFixpoint derive_semantics {i j s} (c : component i j s) (st : s) (sem : semantics j) :=
  mk_semantics (fun (a : Type) (e : i a) =>
                  let out := run_program sem (c a e st) in
                  let res := interp_result out in
                  let sem' := interp_next out in
                  mk_out (fst res) (derive_semantics c (snd res) sem')).

Definition bootstrap {i s} (c : component i ⋄ s) (st : s) :=
  derive_semantics c st semempty.

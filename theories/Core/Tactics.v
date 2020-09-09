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

From ExtLib Require Import Monad.
From ExtLib.Contrib Require Import Monad.
From FreeSpec.Core Require Import Contract ImpureFacts HoareFacts.

Ltac destruct_if_when :=
  let equ_cond := fresh "equ_cond" in
  match goal with
  | |- context[when (negb ?B) _] => case_eq B; intros equ_cond; cbn
  | |- context[when ?B _] => case_eq B; intros equ_cond; cbn
  | |- context[if (negb ?B) then _ else _] => case_eq B; intros equ_cond; cbn
  | |- context[if ?B then _ else _] => case_eq B; intros equ_cond; cbn
  | _ => idtac
  end.

Ltac destruct_if_when_in hyp :=
  let equ_cond := fresh "equ" in
  match type of hyp with
  | context[when (negb ?B) _] => case_eq B;
                                 intro equ_cond;
                                 rewrite equ_cond in hyp
  | context[when ?B _] => case_eq B;
                          intro equ_cond;
                          rewrite equ_cond in hyp
  | context[if (negb ?B) then _ else _] => case_eq B;
                                           intro equ_cond;
                                           rewrite equ_cond in hyp
  | context[if ?B then _ else _] => case_eq B;
                                    intro equ_cond;
                                    rewrite equ_cond in hyp
  | _ => idtac
  end.

Ltac simplify_gens :=
  repeat match goal with
         | H : True |- _ =>
           clear H

         | H: _ /\ _ |- _ =>
           destruct H

         | |- context[@proj_p ?ix ?ix (refl_MayProvide ?ix) _ ?e] =>
           change (@proj_p ix ix (refl_MayProvide ix) _ e) with (Some e);
           cbn match;
           cbn beta

         | H: context[@proj_p ?ix ?ix (refl_MayProvide ?ix) _ ?e] |- _ =>
           change (@proj_p ix ix (refl_MayProvide ix) _ e) with (Some e) in H;
           cbn match in H;
           cbn beta in H

         | |- context[gen_witness_update _ _ _ _] =>
           unfold gen_witness_update;
           repeat (rewrite proj_inj_p_equ || rewrite distinguish)

         | H : context[gen_witness_update _ _ _ _] |- _ =>
           unfold gen_witness_update in H;
           repeat (rewrite proj_inj_p_equ in H || rewrite distinguish in H)

         | |- context[gen_caller_obligation ?c ?ω ?e] =>
           unfold gen_caller_obligation;
           repeat (rewrite proj_inj_p_equ || rewrite distinguish)

         | H : context[gen_caller_obligation ?c ?ω ?e] |- _ =>
           unfold gen_caller_obligation in H;
           repeat (rewrite proj_inj_p_equ in H || rewrite distinguish in H)

         | |- context[gen_callee_obligation ?c ?ω ?e ?x] =>
           unfold gen_callee_obligation;
           repeat (rewrite proj_inj_p_equ || rewrite distinguish)

         | H : context[gen_callee_obligation ?c ?ω ?e ?x] |- _ =>
           unfold gen_callee_obligation in H;
           repeat (rewrite proj_inj_p_equ in H || rewrite distinguish in H)
         end.

#[local]
Ltac prove_impure :=
  repeat (cbn -[
              to_hoare
              gen_caller_obligation
              gen_callee_obligation
              gen_witness_update
          ] in *;
          simplify_gens;
          destruct_if_when);
  lazymatch goal with

  | |- _ /\ _ =>
    split;
    prove_impure

  | |- pre (to_hoare ?c (impure_map ?f ?p)) ?ω =>
    unfold impure_map;
    prove_impure

  | |- pre (to_hoare ?c (impure_apply ?p ?q)) ?ω =>
    unfold impure_map;
    prove_impure

  | |- forall _ _, _ /\ _ = _ -> _ =>
    let x := fresh "x" in
    let ω' := fresh "ω" in
    let o_caller := fresh "o_caller" in
    let equ := fresh "equ" in
    intros x ω' [o_caller equ];
    repeat rewrite equ in *; clear equ; clear ω';
    prove_impure

  | |- pre (to_hoare ?c ?p) ?ω =>
    let p := (eval hnf in p) in
    lazymatch p with
    | request_then ?e ?f =>
      let o_caller := fresh "o_caller" in
      assert (o_caller : gen_caller_obligation c ω e); [ prove_impure
                                                       | constructor; prove_impure
                                                       ]
    | local _ => constructor
    | impure_bind (impure_bind ?p ?f) ?g =>
      rewrite (impure_bind_assoc p f g);
      prove_impure
    | impure_bind ?p ?f =>
      apply to_hoare_pre_bind_assoc; [ eauto with freespec
                                     | let x := fresh "x" in
                                       let ω' := fresh "ω" in
                                       let hpost := fresh "hpost" in
                                       intros x ω' hpost;
                                       prove_impure
                                     ]

    | _ => eauto with freespec
    end

  | |- ?a =>
    eauto with freespec

  end.

Tactic Notation "prove" "impure" := prove_impure.
Tactic Notation "prove" "impure" "with" ident(db) := prove_impure; eauto with db.

Ltac unroll_post_hoare run :=
  repeat (cbn -[
              to_hoare
              gen_caller_obligation
              gen_callee_obligation
              gen_witness_update
          ] in *;
          simplify_gens;
          destruct_if_when_in run);
  lazymatch type of run with

  | post (to_hoare ?c ?p) ?ω ?x ?ω' =>
    let p := (eval hnf in p) in
    lazymatch p with
    | request_then ?e ?f =>
      inversion run; ssubst;
      clear run;
      lazymatch goal with
      | next : exists _, post (interface_to_hoare c _ e) _ _ _ /\ _ |- _ =>
        let ω'' := fresh "ω" in
        let o_callee := fresh "o_callee" in
        let run := fresh "run" in
        destruct next as [ω'' [o_callee run]];
        unroll_post_hoare run
      | _ => idtac
      end

    | local ?x =>
      inversion run; ssubst;
      clear run

    | ?a => idtac
    end

  | ?a => idtac
  end.

(*
(** We first introduce an alternative formalism for reasoning about impure
    computations. It is equivalent to projecting said computations into the
    Hoare monad, but it is more specialized. In practice, it is easier to work
    with this formalism in Coq. *)

Inductive respectful_impure `{MayProvide ix i} {α Ω} (c : contract i Ω) (ω : Ω)
  : impure ix α -> Prop :=

(** - Given a term [x], the computation [local x] is always respectful wrt. [c]
      in accordance to [ω], since it does not use any primitives. *)

| respectful_local (x : α)
  : respectful_impure c ω (local x)

(** - Given a primitive [e] and a continuation [f], if

      - [e] satisfies [c] caller obligation
      - [f] computations are respectful wrt. [c] in accordance to [ω'], where
        [ω'] is the witness updated after [e] interpretation

      then the impure computation [request_then e f] is respectful wrt. [c] in
      accordance to [ω]. *)

| respectful_request_some {β}
    (e : ix β) (f : β -> impure ix α)
    (req : gen_caller_obligation c ω e)
    (next : forall (x : β),
        gen_callee_obligation c ω e x
        -> respectful_impure c (gen_witness_update c ω e x) (f x))
  : respectful_impure c ω (request_then e f).

(** As is, the definition of [respectful_impure] would force FreeSpec users to
    unfold any impure computations they may combine together with [bind].  For
    instance, proving a computation of the form [bind p (λ _, p)] is respectful
    would require to prove [p] is respectful twice, for two different
    witnesses.  Moreover, it could be challenging to know, when interactively
    writing the proof script, when “the first [p]” stops, and when “the second
    [p]” starts.

    We need a way to compose proofs about impure computations the same way we
    compose impure computations with [bind].  We do that with the
    [respectful_run] predicate, which describes the potential outcomes of a
    computation in terms of results and witnesses. *)

Lemma pre_hoare_respectful_impure_equiv `{MayProvide ix i} `(c : contract i Ω)
   `(ρ : impure ix α) (ω : Ω)
  : pre (to_hoare c ρ) ω <-> respectful_impure c ω ρ.

Proof.
  revert ω.
  induction ρ; intros ω.
  + split;
      intros _;
      constructor.
  + split.
    ++ cbn.
       intros [caller next].
       constructor.
       +++ exact caller.
       +++ intros x callee.
           rewrite <- H0.
           apply next.
           split; [apply callee | reflexivity].
    ++ intros respect.
       inversion respect; ssubst.
       cbn.
       split; [apply req |].
       intros x ω' [callee equ].
       rewrite equ.
       rewrite H0.
       apply next.
       exact callee.
Qed.

Inductive respectful_run `{MayProvide ix i} {α Ω} (c : contract i Ω)
  : impure ix α -> Ω -> Ω -> α -> Prop :=

(** Given a term [x], and an initial witness [ω], a respectful run of
    [local x] produced a result [x] and a witness state [ω]. *)

| run_local (x : α) (ω : Ω)
  : respectful_run c (local x) ω ω x

(** Given an initial witness [ω], a primitive [e] which satisfies [c]
    caller obligations, and a continuation [f], a result [x] for [e] which
    satisfies [c] callee obligations, if we can show that there is a respectful
    run of [f x] which produces a term [y] and a witness [ω'], then there is a
    respectful run of [request_then e f] which produces a result [y] and a
    witness [ω']. *)

| run_request {β} (ω : Ω)
    (e : ix β) (o_caller : gen_caller_obligation c ω e) (f : β -> impure ix α)
    (x : β) (o_callee : gen_callee_obligation c ω e x)
    (ω' : Ω) (y : α) (rec : respectful_run c (f x) (gen_witness_update c ω e x) ω' y)
  : respectful_run c (request_then e f) ω ω' y.

Lemma post_hoare_respectful_run_equiv `{MayProvide ix i} `(c : contract i Ω)
   `(ρ : impure ix α) (ω ω' : Ω) (x : α)
    (hpre : pre (to_hoare c ρ) ω)
  : (post (to_hoare c ρ) ω x ω') <-> respectful_run c ρ ω ω' x.

Proof.
  revert ω hpre.
  induction ρ; intros ω hpre.
  + split; cbn.
    ++ intros [equ1 equ2]; subst.
       constructor.
    ++ intros run.
       now inversion run; subst.
  + split.
    ++ intros hpost.
       destruct hpre as [caller next].
       cbn in hpost.
       destruct hpost as [y [ω'' [[callee equ] hpost]]]; subst.
       apply run_request with (x0:=y).
       +++ apply caller.
       +++ apply callee.
       +++ apply H0; [| apply hpost].
           apply next.
           cbn.
           split; [apply callee| reflexivity].
    ++ intros run.
       inversion run; ssubst.
       cbn.
       exists x0.
       exists (gen_witness_update c ω e x0).
       split; [split |].
       +++ apply o_callee.
       +++ reflexivity.
       +++ apply H0; [now apply hpre |].
           apply rec.
Qed.

Lemma respectful_bind_exists_respectful_run `{MayProvide ix i} {α β Ω}
    (c : contract i Ω) (ω ω' : Ω)
    (p : impure ix α) (f : α -> impure ix β) (x : β)
    (respect : respectful_run c (impure_bind p f) ω ω' x)
  : exists (ω'' : Ω) (y : α),
    respectful_run c p ω ω'' y /\ respectful_run c (f y) ω'' ω' x.

Proof.
  revert respect.
  revert ω ω'.
  induction p; intros ω ω' respect.
  + exists ω; exists x0.
    split.
    ++ constructor.
    ++ exact respect.
  + inversion respect; ssubst.
    apply H0 in rec.
    destruct rec as [ω'' [y [trust1 trust2]]].
    exists ω''; exists y.
    split; auto.
    constructor 2 with (x := x0); auto.
Qed.

(** The [impure] monad is an empty shell which brings structure and only that.
    It is not relevant when it comes to verifying impure computations, and we
    provide a tactic called [prove_impure] to erase it while proving a given
    impure computation is respectful wrt. to a given contract. *)

Lemma respectful_bind_respectful_run `{MayProvide ix i} {α β Ω}
  (c : contract i Ω) (ω : Ω)
  (p : impure ix α) (f : α -> impure ix β)
  (respect : respectful_impure c ω p)
  (run : forall (x : α) (ω' : Ω),
      respectful_run c p ω ω' x -> respectful_impure c ω' (f x))
  : respectful_impure c ω (impure_bind p f).

Proof.
  revert ω respect run.
  induction p; intros ω respect run.
  + apply run.
    constructor.
  + cbn.
    inversion respect; ssubst.
    constructor.
    ++ apply req.
    ++ intros y o_callee_x.
       apply H0; [ auto |].
       intros z ω' run'.
       apply run.
       econstructor; eauto.
Qed.

Ltac prove_impure_aux :=
  repeat (cbn -[gen_caller_obligation gen_callee_obligation gen_witness_update]; destruct_if_when);
  lazymatch goal with

  | H : ?a |- ?a => exact H

  | |- _ /\ _ => split; prove_impure_aux
  | H : _ /\ _ |- _ => destruct H; prove_impure_aux
  | H : True |- _ => clear H; prove_impure_aux

  | |- context[gen_witness_update _ _ _ _] =>
    unfold gen_witness_update;
    repeat (rewrite proj_inj_p_equ || rewrite distinguish);
    prove_impure_aux

  | H : context[gen_witness_update _ _ _ _] |- _ =>
    unfold gen_witness_update in H;
    repeat (rewrite proj_inj_p_equ in H || rewrite distinguish in H);
    prove_impure_aux

  | |- respectful_impure ?c ?w (impure_map ?f ?p) =>
    unfold impure_map;
    prove_impure_aux

  | |- respectful_impure ?c ?w (impure_bind (impure_bind ?p ?f) ?g) =>
    rewrite (impure_bind_assoc p f g);
    prove_impure_aux

  | |- respectful_impure ?c ?w (impure_bind ?p ?f) =>
    let x := fresh "x" in
    let w := fresh "w" in
    let Hrun := fresh "Hrun" in
    apply respectful_bind_respectful_run; [ | intros x w Hrun;
                                              prove_impure_aux ]


  | |- respectful_impure _ _ (local _) => constructor
  | |- respectful_impure _ _ (impure_pure _) => constructor

  | |- respectful_impure ?c ?w ?p =>
    let p := (eval hnf in p) in
    match p with
    | request_then ?e _ =>
      let o_caller := fresh "o_caller" in
      assert (o_caller : gen_caller_obligation c w e); [ prove_impure_aux
                                                       | constructor; prove_impure_aux
                                                       ]
    | _ => idtac
    end
  | |- context[gen_caller_obligation _ _ _] =>
    unfold gen_caller_obligation;
    repeat (rewrite proj_inj_p_equ || rewrite distinguish);
    prove_impure_aux
  | H: context[gen_caller_obligation _ _ _] |- _ =>
    cbn in H;
    unfold gen_caller_obligation in H;
    repeat (rewrite proj_inj_p_equ in H || rewrite distinguish in H);
    prove_impure_aux

  | |- forall _, gen_callee_obligation _ _ _ _ -> _ =>
    let x := fresh "x" in
    let o_caller := fresh "o_caller" in
    intros x o_caller;
    cbn in o_caller;
    unfold gen_callee_obligation in o_caller;
    repeat (rewrite proj_inj_p_equ in o_caller || rewrite distinguish in o_caller);
    prove_impure_aux

  | |- ?a => auto
  end.

Ltac prove_impure := apply pre_hoare_respectful_impure_equiv; prove_impure_aux.

Ltac simpl_gens :=
  cbn in *;
  repeat lazymatch goal with
         | H : gen_caller_obligation _ _ _ /\ gen_caller_obligation _ _ _ |- _ =>
           destruct H
         | H : gen_callee_obligation _ _ _ _ /\ gen_callee_obligation _ _ _ _ |- _ =>
           destruct H
         end;
  repeat unfold gen_caller_obligation in *;
  repeat unfold gen_callee_obligation in *;
  repeat unfold gen_witness_update in *;
  repeat
    lazymatch goal with
    | H : context[proj_p (inj_p ?e)] |- _ =>
      (rewrite proj_inj_p_equ in H || rewrite distinguish in H);
      cbn in H
    | |- context[proj_p (inj_p ?e)] =>
      (rewrite proj_inj_p_equ || rewrite distinguish); cbn
    end;
  repeat
    lazymatch goal with
    | H : True |- _ => clear H
    end.

Ltac unroll_respectful_run_aux run :=
  repeat (cbn -[gen_witness_update gen_caller_obligation gen_callee_obligation] in run; destruct_if_when_in run);
  lazymatch type of run with
  | respectful_run _ (impure_pure _) _ _ _ =>
    inversion run; ssubst; clear run
  | respectful_run _ (local _) _ _ _ =>
    inversion run; ssubst; clear run

  | respectful_run ?c (request_then ?e ?f) ?init ?final ?res =>
    inversion run; ssubst;
    clear run;
    lazymatch goal with
    | next : respectful_run c _ _ final res |- _ =>
      unroll_respectful_run_aux next
    | |- _ => fail "unexpected error, consider reporting the issue"
    end

  | respectful_run ?c (impure_map ?f ?p) ?init ?final ?res =>
    unfold impure_map in run;
    unroll_respectful_run_aux run

  | respectful_run ?c (impure_bind (impure_bind ?p ?f) ?g) ?init ?final ?res =>
    rewrite (impure_bind_assoc p f g) in run;
    unroll_respectful_run_aux run

  | respectful_run ?c (impure_bind ?p ?f) ?init ?final ?res =>
    apply (respectful_bind_exists_respectful_run c init final p f res) in run;
    let run1 := fresh "run" in
    let run2 := fresh "run" in
    destruct run as [?ω'' [?y [run1 run2]]];
    unroll_respectful_run_aux run1; unroll_respectful_run_aux run2

  | respectful_run ?c ?p ?init ?final ?res =>
    lazymatch (eval compute -[inj_p] in p) with
    | request_then ?e ?f =>
      inversion run; ssubst;
      clear run;
      lazymatch goal with
      | next : respectful_run c _ _ final res |- _ =>
        unroll_respectful_run_aux next
      | |- _ => idtac
      end
    | _ => idtac
    end

  | ?e => fail "cannot handle goal of the form" e
  end.

Ltac unroll_respectful_run run :=
  apply post_hoare_respectful_run_equiv in run; [
    unroll_respectful_run_aux run;
    simpl_gens
   |]; try rewrite <- post_hoare_respectful_run_equiv.

Tactic Notation "prove" "impure" "with" ident(db) := prove_impure; eauto with db.
*)

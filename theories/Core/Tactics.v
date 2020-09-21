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

Ltac unroll_post run :=
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
        unroll_post run
      | _ => idtac
      end

    | local ?x =>
      inversion run; ssubst;
      clear run

    | impure_bind ?p ?f =>
      apply (to_hoare_post_bind_assoc c p f) in run;
      let run1 := fresh "run" in
      let run2 := fresh "run" in
      let x := fresh "x" in
      let ω := fresh "ω" in
      destruct run as [x [ω [run1 run2]]];
      unroll_post run1; unroll_post run2

    | ?a => idtac
    end

  | ?a => idtac
  end.

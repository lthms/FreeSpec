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

From Prelude Require Import All.
From FreeSpec.Core Require Import Contract.

(** The [impure] monad is an empty shell which brings structure and only that.
    It is not relevant when it comes to verifying impure computations, and we
    provide a tactic called [prove_impure] to erase it while proving a given
    impure computation is respectful wrt. to a given contract. *)

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

Ltac prove_impure :=
  repeat (cbn -[gen_caller_obligation gen_callee_obligation gen_witness_update]; destruct_if_when);
  lazymatch goal with

  | H : ?a |- ?a => exact H

  | |- _ /\ _ => split; prove_impure
  | H : _ /\ _ |- _ => destruct H; prove_impure
  | H : True |- _ => clear H; prove_impure

  | |- context[gen_witness_update _ _ _ _] =>
    unfold gen_witness_update;
    repeat (rewrite proj_inj_p_equ || rewrite distinguish);
    prove_impure

  | H : context[gen_witness_update _ _ _ _] |- _ =>
    unfold gen_witness_update in H;
    repeat (rewrite proj_inj_p_equ in H || rewrite distinguish in H);
    prove_impure

  | |- respectful_impure ?c ?w (impure_map ?f ?p) =>
    unfold impure_map;
    prove_impure

  | |- respectful_impure ?c ?w (impure_bind (impure_bind ?p ?f) ?g) =>
    rewrite (impure_bind_assoc p f g);
    prove_impure

  | |- respectful_impure ?c ?w (impure_bind ?p ?f) =>
    let x := fresh "x" in
    let w := fresh "w" in
    let Hrun := fresh "Hrun" in
    apply respectful_bind_respectful_run; [| intros x w Hrun;
                                             prove_impure ]


  | |- respectful_impure _ _ (local _) => constructor
  | |- respectful_impure _ _ (impure_pure _) => constructor

  | |- respectful_impure ?c ?w ?p =>
    let p := (eval hnf in p) in
    match p with
    | request_then ?e _ =>
      let o_caller := fresh "o_caller" in
      assert (o_caller : gen_caller_obligation c w e); [ prove_impure
                                                       | constructor; prove_impure
                                                       ]
    | _ => idtac
    end
  | |- context[gen_caller_obligation _ _ _] =>
    unfold gen_caller_obligation;
    repeat (rewrite proj_inj_p_equ || rewrite distinguish);
    prove_impure
  | H: context[gen_caller_obligation _ _ _] |- _ =>
    cbn in H;
    unfold gen_caller_obligation in H;
    repeat (rewrite proj_inj_p_equ in H || rewrite distinguish in H);
    prove_impure

  | |- forall _, gen_callee_obligation _ _ _ _ -> _ =>
    let x := fresh "x" in
    let o_caller := fresh "o_caller" in
    intros x o_caller;
    cbn in o_caller;
    unfold gen_callee_obligation in o_caller;
    repeat (rewrite proj_inj_p_equ in o_caller || rewrite distinguish in o_caller);
    prove_impure

  | |- ?a => auto
  end.

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

Ltac unroll_respectful_run run := unroll_respectful_run_aux run; simpl_gens.

Tactic Notation "prove" "impure" "with" ident(db) := prove_impure; eauto with db.

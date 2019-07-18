(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2018 Thomas Letan <thomas.letan@ssi.gouv.fr>
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

Require Import Prelude.Control.
Require Import FreeSpec.Program.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Specification.

Ltac next := repeat (try constructor; cbn; trivial).

Ltac destruct_if_when :=
  match goal with
  | [ |- context[when (negb ?B) _]]
    => let eq_cond := fresh "Heq_cond"
       in case_eq B; intros eq_cond; cbn
  | [ |- context[when ?B _]]
    => let eq_cond := fresh "Heq_cond"
       in case_eq B; intros eq_cond; cbn
  | [ |- context[if (negb ?B) then _ else _]]
    => let eq_cond := fresh "Heq_cond"
       in case_eq B; intros eq_cond; cbn
  | [ |- context[if ?B then _ else _]]
    => let eq_cond := fresh "Heq_cond"
       in case_eq B; intros eq_cond; cbn
  | _
    => idtac
  end.

Ltac run_program sig :=
  match goal with
  | [ H : sig |= ?spec [ ?state ] |- context[handle sig ?eff] ]
    =>  let i := fresh "i" in
        let Hreq_i    := fresh "Hreq_i"    in
        let Hprom_i   := fresh "Hprom_i"   in
        let int       := fresh "int"       in
        let Heq_int   := fresh "Heq_int"   in
        let Henf_int  := fresh "Henf_inf"  in
        let abs       := fresh "abs"       in
        let Heq_abs   := fresh "Heq_abs"   in
        let res       := fresh "res"       in
        let Heq_res   := fresh "Heq_res"   in
        remember (eff) as i;
        cut (precondition spec i state); [
          intro Hreq_i;
          remember (Sem.res (handle sig i)) as res eqn: Heq_res;
          assert (Hprom_i:  postcondition spec i res state)
            by (rewrite Heq_res; apply H; exact Hreq_i);
          remember (Sem.next (handle sig i)) as int eqn: Heq_int;
          remember (abstract_step spec i res state) as abs eqn: Heq_abs;
          assert (Henf_int:  int |= spec [abs])
            by (rewrite Heq_abs;
                rewrite Heq_int;
                apply H;
                exact Hreq_i);
          run_program int
         |]
  | _
    => idtac
  end.

Ltac simplify_postcondition :=
  match goal with
  | [ Hres:  ?res = Sem.res (handle _ ?eff) |- _]
    => match goal with
       | [ Heff:  eff = _ |- _ ]
         => match goal with
            | [ Hprom:  postcondition _ eff _ _ |- _ ]
              => rewrite Heff in Hprom;
                 cbn in Hprom
            end
       end
  end.

(** The [prove_program] can be used with a goal of the form [?p |> ?c[?w]], that
    is proving that a program is correct wrt. an abstract specification. Its
    main benefit it to erase the Program monad. *)
Ltac prove_program :=
  repeat (cbn; destruct_if_when);
  lazymatch goal with
  (* 1st case: nested bind:
       rewrite ((p >>= f) >>= g) into p >>= (λ x, f x >>= g) *)
  | |- program_bind (program_bind ?p ?f) ?g |> ?c[?w]
    => rewrite (program_eq_bind_assoc p f g); prove_program
  (* 2nd case: bind opaque program:
       rely on the correct_run abstraction *)
  | |- program_bind ?p ?f |> ?c [?w]
    => let x := fresh "x" in
       let w := fresh "w" in
       let Hrun := fresh "Hrun" in
       apply correct_program_correct_run_correct_bind; [| intros x w Hrun;
                                                          prove_program ]
  (* 3rd case: request constructor
      generate a gool to prove the effect satisfies the precondition *)
  | |- Request ?e ?f |> ?c[?w]
    => let Hpre := fresh "Hpre" in
       assert (Hpre: precondition c e w); [| constructor; [apply Hpre |];
                                             let sig := fresh "sig" in
                                             let Hsig := fresh "Hsig" in
                                             let res := fresh "res" in
                                             let Hpost := fresh "Hpost" in
                                             intros res Hpost;
                                             prove_program ]
  (* 4st case: pure constructor
       conclude *)
  | |- Pure ?x |> ?c[?w]
    => constructor
  | |- program_pure ?x |> ?c[?w]
    => constructor
  | _
    => fail "Unexpected goal: prove_program allows for proving program correctness"
  end.

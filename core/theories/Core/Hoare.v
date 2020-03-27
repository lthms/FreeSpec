(* FreeSpec
 * Copyright (C) 2018–2020 ANSSI
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

From Prelude Require Import All.
From FreeSpec Require Import Impure Contract Morphism Tactics.

(** If we consider the monad form by the set of sets of predicates, that is

<<
Definition predicate (a : Type) : Type := a -> Prop.
>>

    whose [bind] and [pure] functions is defined as follows

<<
Definition predicat_bind {α β} (p : predicate α) (f : α -> predicate β)
  : predicate β :=
  fun r => exists (x : α), p x /\ (f x) r.

Definition predicat_pure {α} (x : α) : predicate α := eq x.
>>

    Then, given [f := fun α e => fun x => True] the morphism from the interface
    type [i] to [predicate] such that [f α e] is a predicate which is always
    satisfied, [morphism_lift f p] is a predicate which allows for reasoning
    about any potential output of [p] (that is, considering any implementer for
    [i]).

    The [hoare] monad is another interesting candidate for reifying our [impure]
    monad, and we demonstrate here that we can easily provide a morphism from
    [impure] to [hoare], to the extent that we provide a contract to generate
    the [pre] and [post] condition of the hoare monad.

    We define the [hoare_of_contract] morphism parameterized by a contract [c]
    to project primitives of an interface to the [hoare] monad. This morphism
    use the obligations of [c] to define the precondition and postcondition of
    the resulting [hoare] monadic term. *)

Definition hoare_of_contract `{MayProvide ix i} {Ω} (c : contract i Ω)
  : ix ~> hoare Ω :=
  fun α (e : ix α) =>
    mk_hoare (fun ω => gen_caller_obligation c ω e)
             (fun ω x ω' =>
                gen_callee_obligation c ω e x
                /\ ω' = gen_witness_update c ω e x).

Definition hoare_of_impure `{MayProvide ix i} {Ω} (c : contract i Ω)
  : impure ix ~> hoare Ω :=
  morphism_lift (hoare_of_contract c).

Arguments hoare_of_impure {ix i H Ω} (c) {α} _.

(** Then, we demonstrate that, considering [hp] the (hoare) monad computed
    thanks to [hoare_of_contract] and [morphism_lift], and an impure computation
    [p]

      - [respectful_impure_equivalence]: If a witness state [ω] satisfies the
        pre condition of [hp], then [p] is respectful wrt. [c] in accordance to
        [ω] (see [respectful_impure]).
      - [respectful_run_equivalence]: Similarly, if a tuple [(ω, x, ω')]
        satisfies the post condition [hp], then there exists a respectful run
        from [ω] to compute [x] and [ω'] (see [respectful_run]). *)

Lemma respectful_impure_equivalence  `{MayProvide ix i} {α Ω}
    (c : contract i Ω) (ω : Ω) (p : impure ix α)
  : respectful_impure c ω p <-> pre (hoare_of_impure c p) ω.

Proof.
  revert ω.
  induction p; intros ω.
  + split; cbn.
    ++ auto.
    ++ intros _.
       constructor.
  + cbn.
    split.
    ++ intros r.
       inversion r; ssubst.
       split; [ exact req |].
       intros x s'.
       intros [post equ].
       specialize next with x.
       apply next in post.
       apply H0 in post.
       rewrite equ.
       apply post.
    ++ intros [p r1].
       constructor; [ exact p |].
       intros x q.
       rewrite H0.
       apply r1.
       split; [ exact q | reflexivity ].
Qed.

Lemma respectful_run_equivalence  `{MayProvide ix i} {α Ω}
    (c : contract i Ω) (p : impure ix α) (ω : Ω) (x : α) (ω' : Ω)
    (h : respectful_impure c ω p)
  : respectful_run c p ω ω' x <-> post (hoare_of_impure c p) ω x ω'.

Proof.
  revert ω ω' x h.
  induction p; intros ω ω' r h.
  + split; cbn.
    ++ intros run.
       unroll_respectful_run run; auto.
    ++ intros [r1 r2].
       subst.
       constructor.
  + inversion h; ssubst.
    split.
    ++ intros run.
       inversion run; ssubst.
       cbn.
       exists x.
       exists (gen_witness_update c ω e x).
       repeat split; auto.
       apply H0; auto.
    ++ intros [t [ω'' [[r1 r2] r3]]]; subst.
       econstructor.
       +++ apply req.
       +++ apply r1.
       +++ apply H0; auto.
Qed.

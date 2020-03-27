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
From FreeSpec Require Import Impure Contract Tactics.
From FreeSpec Require Export Hoare.Monad.

(** In _Dijkstra Monads for Free_, Ahman et al. explore the idea of “reifying”
    computations encoded in an “effectful” computation into a “specification”
    monad, more suitable for reasoning.

    From a high-level perspective, a reification function from a computation
    into a monad [m] to another monad [w] is a morphism to project terms of [m
    a] (for any [a]) to terms of [w a]. *)

Definition second_order_morphism (m : Type -> Type) (w : Type -> Type) :=
  forall (α : Type), m α -> w α.

Infix "~>" := second_order_morphism (at level 80, no associativity) : type_scope.

(** Interestingly, FreeSpec provides since the very start an example of such a
    function: [run_impure]. Indeed, what [run_impure] actually does is reifying
    a computation encoded in the [impure] monad to the [state] monad, which is a
    pure, computable value as far as Coq is concerned. *)

Definition run_impure_reify {i} : impure i ~> state (semantics i) :=
  fun _ p sem => (fun x => (interp_result x, interp_next x)) $ run_impure sem p.

(** Even more interesting: the definition of [impure] allows us to consider a
    more general approach to construct morphism from [impure] to a monad [w]. We
    just need to have a morphism from the interface type [i] to the monad
    [w]. *)

Definition morphism_lift `{Monad w} {i} (s : i ~> w) : impure i ~> w :=
  fix rec (α : Type) (p : impure i α) :=
    match p with
    | local x => pure x
    | request_then e f => bind (s _ e) (fun x => rec α (f x))
    end.

(** This allows for neat tricks.

    For instance, [run_impure_reify] (and therefore [run_impure]) can be
    reimplemented using [run_effect] and [morphism_lift]. *)

Definition run_impure_reify' {i} : impure i ~> state (semantics i) :=
  morphism_lift
    (fun* _ e sem =>
       (fun x => (interp_result x, interp_next x)) <$> run_effect sem e).

Lemma run_impure_equiv `{Equality α} {i} (p : impure i α)
  : run_impure_reify _ p == run_impure_reify' _ p.

Proof.
  induction p.
  + reflexivity.
  + intros sem.
    replace (run_impure_reify α (request_then e f) sem)
      with (run_impure_reify α (f (interp_result $ run_effect sem e))
                             (interp_next $ run_effect sem e)); [| reflexivity].
    replace (run_impure_reify' α (request_then e f) sem)
      with (run_impure_reify' α (f (interp_result $ run_effect sem e))
                             (interp_next $ run_effect sem e)); [| reflexivity].
    apply H0.
Qed.

(** But we can also consider other monads, more suitable for reasoning about
    impure computations. In particular, the [hoare] monad allows for reasoning
    about impure computations in terms of precondition and postcondition. *)

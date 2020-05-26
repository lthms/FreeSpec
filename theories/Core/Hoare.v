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

From ExtLib Require Import Functor Applicative Monad.
From FreeSpec.Core Require Import Interface Impure Contract.

(** To reason about impure computations, we introduce the “Hoare
    monad,” also called the “specification monad.” An instance of the
    specification monad is a couple of [pre] and [post] conditions,
    such that [pre p σ] means the program specified by [p] can be
    executed safely from a state [σ], and [post p σ x σ'] means the
    execution of [p] from [σ] may compute a result [x] and bring the
    system to a state [σ'].

    We equip this couple of predicate with a [bind] function to
    sequentially compose specifications. *)

(** * Definition *)

Record hoare (Σ : Type) (α : Type) : Type :=
  mk_hoare { pre : Σ -> Prop
           ; post : Σ -> α -> Σ -> Prop
           }.

Arguments mk_hoare {Σ α} (pre post).
Arguments pre {Σ α} (_ _).
Arguments post {Σ α} (_ _ _).

Definition hoare_pure {Σ α} (x : α) : hoare Σ α :=
  mk_hoare (fun _ => True) (fun s y s' => x = y /\ s = s').

Definition hoare_bind {Σ α β} (h : hoare Σ α) (k : α -> hoare Σ β) : hoare Σ β :=
  mk_hoare (fun s => pre h s /\ (forall x s', post h s x s' -> pre (k x) s'))
           (fun s x s'' => exists y s', post h s y s' /\ post (k y) s' x s'').

(** * Instances *)

(** ** Functor *)

Definition hoare_map {Σ α β} (f : α -> β) (h : hoare Σ α) : hoare Σ β :=
  hoare_bind h (fun x => hoare_pure (f x)).

Instance hoare_Functor Σ : Functor (hoare Σ) :=
  { fmap := fun _ _ => hoare_map }.

(** ** Applicative *)

Definition hoare_apply {Σ α β} (hf : hoare Σ (α -> β)) (h : hoare Σ α)
  : hoare Σ β :=
  hoare_bind hf (fun f => hoare_map f h).

Instance hoare_Applicative : Applicative (hoare Σ) :=
  { ap := fun _ _ => hoare_apply
  ; pure := fun _ => hoare_pure
  }.

(** ** Monad *)

Instance hoare_Monad Σ : Monad (hoare Σ) :=
  { ret := @hoare_pure Σ; bind := @hoare_bind Σ }.

(** * Reasoning about Programs *)

Definition interface_to_hoare `{MayProvide ix i} `(c : contract i Ω) : ix ~> hoare Ω :=
  fun a e =>
    {| pre := fun ω => gen_caller_obligation c ω e
     ; post := fun ω x ω' => gen_callee_obligation c ω e x
                             /\ ω' = gen_witness_update c ω e x
    |}.

Definition to_hoare `{MayProvide ix i} `(c : contract i Ω)
  : impure ix ~> hoare Ω :=
  impure_lift (interface_to_hoare c).

Arguments to_hoare {ix i _ Ω} c {α} _.

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

From Coq Require Import Arith.
From FreeSpec Require Import Core.

(** * Specifying

    ** Door *)

Inductive DOOR {l} (d : l) : interface :=
| IsOpen : DOOR d bool
| Toggle : DOOR d unit.

Definition is_open {ix l} (d : l) `{ix :| DOOR d} : program ix bool :=
  request (IsOpen d).

Definition toggle {ix l} (d : l) `{ix :| DOOR d} : program ix unit :=
  request (Toggle d).

Definition open_door {ix l} (d : l) `{ix :| DOOR d} : program ix unit :=
  var open ← is_open d in
  when (negb open) (toggle d).

Definition close_door {ix l} (d : l) `{ix :| DOOR d} : program ix unit :=
  var open ← is_open d in
  when open (toggle d).

(** ** Controller *)

Inductive door : Type := left | right.

Inductive CONTROLLER : interface :=
| Tick : CONTROLLER unit
| RequestOpen (d : door) : CONTROLLER unit.

Definition tick {ix} `{ix :| CONTROLLER} : program ix unit :=
  request Tick.

Definition request_open {ix} `{ix :| CONTROLLER} (d : door) : program ix unit :=
  request (RequestOpen d).

Definition co (d : door) : door :=
  match d with
  | left => right
  | right => left
  end.

Instance door_Provide (d : door) : Provide (DOOR left ⊕ DOOR right) (DOOR d) :=
  { lift_eff := match d with
                | left => fun _ op => in_left op
                | right => fun _ op => in_right op
                end
  }.

From Prelude Require Import State.

Definition controller : component CONTROLLER (DOOR left ⊕ DOOR right) nat :=
  fun _ op =>
    match op with
    | Tick =>
      var cpt ← get in
      when (15 <? cpt) $ do lift (close_door left);
                            lift (close_door right);
                            put 0
    | RequestOpen d =>
      do lift (close_door (co d));
         lift (open_door d);
         put 0
    end.

(** * Verifying *)

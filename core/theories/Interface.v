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

(** * Regural [Interface]s

    We consider an [Interface] to be a set of _operations_ whose
    result type only is known. This is usually encoded thanks to a
    parameterized type in functional programming language, where the
    type parameter is the type of the result. *)

Definition Interface := Type -> Type.

(** That is, if [I] is an interface, [o : I A] is an operation whose
    result (computed by a handler) is expected to be of type [A]. *)

(** * Labeled [Interface]s

    We can label an interface with a particular type to enrich a
    primitive call with a context. The main idea is this label will be
    stripped before extraction.

 *)

Inductive LabeledInterface
          (I: Interface)
          (L: Type)
  : Interface :=
| labeled_instruction (A: Type)
                      (i: I A)
                      (l: L)
  : LabeledInterface I L A.

Arguments labeled_instruction [I L A] (i l).

Infix "<?>" := LabeledInterface
  (at level 32, no associativity)
  : free_scope.

Infix "<:>" := labeled_instruction
  (at level 32, no associativity)
  : free_scope.
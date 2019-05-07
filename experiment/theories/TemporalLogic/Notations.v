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

Require Import Experiment.TemporalLogic.

(** We define several notation to make a formula more readable. These
    notations are obviously optional, but they can help to have a
    cleaner code. The risk, however, is that you code will not be
    readable if the unicode characters are not supported by the font
    used to render them.

 *)

Notation "⬜ p" := (globally p) (at level 70): formula_scope.
Notation "◊ p" := (eventually p) (at level 70): formula_scope.
Notation "⃝ p" := (next p) (at level 70): formula_scope.
Notation "⟙" := (ltrue) (at level 70): formula_scope.
Notation "⟘" := (lfalse) (at level 70): formula_scope.
Notation "f1 ⊢ p ⟶ f2" := (switch f1 p f2) (at level 70): formula_scope.
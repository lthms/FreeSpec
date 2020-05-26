(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2019 Thomas Letan <thomas.letan@ssi.gouv.fr>
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

From Base Require Import Prelude Extraction.
From FreeSpec.Core Require Import All Extraction.
From FreeSpec.Stdlib Require Import Console.

Generalizable All Variables.

Definition pipe `{Provide2 ix FILES (RAISE file_err)} : impure ix unit :=
  scan >>= echo.

Definition main : unit := eval_impure FilesExtr.files (halt_on_error pipe).

Extraction "pipe.ml" main.

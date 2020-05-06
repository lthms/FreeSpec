(* FreeSpec
 * Copyright (C) 2018–2020 ANSSI
 *
 * Contributors:
 * 2020 Thomas Letan <thomas.letan@ssi.gouv.fr>
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
From FreeSpec.Core Require Import All.
From FreeSpec.Exec Require Import All Heap.
From FreeSpec.Stdlib Require Import Console.

Definition play_with_heap `{Provide ix HEAP, Provide ix CONSOLE} : impure ix unit :=
  do let* ptr := new_ref 2 in
     assign ptr 3;
     let* x := deref ptr in
     if x ?= 2
     then echo "yes!\n"
     else echo "no!\n"
  end.

(* should print "no!" *)
Exec play_with_heap.

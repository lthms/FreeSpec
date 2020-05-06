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

From FreeSpec.Exec Require Import All.
From FreeSpec Require Import Console Files Raise.

Definition read_print `{Provide2 ix FILES CONSOLE} : impure ix unit :=
  recover do
      let* fd := try_open "tests/files.v" in
      let* res := try_read fd 100 in
      echo (snd res);
      close fd
  end with
    err of _ => echo "something went wrong"
  end.

Exec read_print.

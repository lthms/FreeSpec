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

val char_of_coqascii: Constr.constr -> char
val char_to_coqascii: char -> Constr.constr

val bytes_of_coqstr: Constr.constr -> bytes
val bytes_to_coqstr: bytes -> Constr.constr

val string_to_coqstr: string -> Constr.constr
val string_of_coqstr: Constr.constr -> string

val coqstr_t : Constr.constr

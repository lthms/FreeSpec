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

exception Anomaly of string
exception UnsupportedTerm of string
exception UnsupportedInterface
exception NotImplementedYet

let notice str =
  Feedback.msg_notice (Pp.strbrk str)

let app_full trm =
  let rec aux trm acc =
    match Constr.kind trm with
    | Constr.App (f, xs)
      -> aux f (Array.to_list xs @ acc)
    | _
      -> (trm, acc)
  in aux trm []

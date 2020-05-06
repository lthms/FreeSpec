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

type store = (int, Obj.t) Hashtbl.t

let vault : store = Hashtbl.create ~random:false 10
let count = ref 0

let insert v = begin
  let k = !count in
  count := !count + 1;
  Hashtbl.add vault k (Obj.repr v);
  k
end

let remove k = begin
  Hashtbl.remove vault k
end

let replace k v = Hashtbl.replace vault k (Obj.repr v)

let find k = Obj.obj (Hashtbl.find vault k)

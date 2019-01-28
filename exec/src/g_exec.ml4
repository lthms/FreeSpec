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

DECLARE PLUGIN "exec"

open Stdarg

VERNAC COMMAND EXTEND Exec CLASSIFIED AS SIDEFF
    | [ "Exec" constr(def) ] ->
    [ let (evm, env) = Pfedit.get_current_context () in
      let (def, _) = Constrintern.interp_constr env evm def in
      let def = EConstr.to_constr evm def in
      Exec.exec env evm def
    ]
END;;

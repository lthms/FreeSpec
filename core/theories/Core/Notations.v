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

From FreeSpec.Core Require Import Impure.

Generalizable All Variables.

Class Provide2 ix i1 i2 `{Provide ix i1, Provide ix i2}.

#[program]
Instance Make_Provide2 `(Provide ix i1, Provide ix i2)
  : Provide2 ix i1 i2.

Class Provide3 ix i1 i2 i3 `{Provide ix i1, Provide ix i2, Provide ix i3}.

#[program]
Instance Make_Provide3 `(Provide ix i1, Provide ix i2, Provide ix i3)
  : Provide3 ix i1 i2 i3.

Class Provide4 ix i1 i2 i3 i4
   `{Provide ix i1, Provide ix i2, Provide ix i3, Provide ix i4}.

#[program]
Instance Make_Provide4 `{Provide ix i1, Provide ix i2, Provide ix i3, Provide ix i4}
  : Provide4 ix i1 i2 i3 i4.

Class Provide5 ix i1 i2 i3 i4 i5
   `{Provide ix i1, Provide ix i2, Provide ix i3, Provide ix i4, Provide ix i5}.

#[program]
Instance Make_Provide5
   `{Provide ix i1 , Provide ix i2, Provide ix i3, Provide ix i4, Provide ix i5}
  : Provide5 ix i1 i2 i3 i4 i5.

Class StrictProvide2 ix i1 i2
   `{Provide ix i1, Provide ix i2, ! Distinguish ix i1 i2, ! Distinguish ix i2 i1}.

#[program]
Instance Make_StrictProvide2
   `(Provide ix i1,  Provide ix i2, ! Distinguish ix i1 i2, ! Distinguish ix i2 i1)
  : StrictProvide2 ix i1 i2.

Class StrictProvide3 (ix i1 i2 i3 : interface)
  `{Provide ix i1, Provide ix i2, Provide ix i3, ! Distinguish ix i1 i2,
    ! Distinguish ix i1 i3, ! Distinguish ix i2 i1, ! Distinguish ix i2 i3,
    ! Distinguish ix i3 i1, ! Distinguish ix i3 i2}.

#[program]
Instance Make_StrictProvide3
  `(Provide ix i1, Provide ix i2, Provide ix i3, ! Distinguish ix i1 i2,
    ! Distinguish ix i1 i3, ! Distinguish ix i2 i1, ! Distinguish ix i2 i3,
    ! Distinguish ix i3 i1, ! Distinguish ix i3 i2)
  : StrictProvide3 ix i1 i2 i3.

Class StrictProvide4 (ix i1 i2 i3 i4 : interface)
  `{Provide ix i1, Provide ix i2, Provide ix i3, Provide ix i4,
    ! Distinguish ix i1 i2, ! Distinguish ix i1 i3, ! Distinguish ix i1 i4,
    ! Distinguish ix i2 i1, ! Distinguish ix i2 i3, ! Distinguish ix i2 i4,
    ! Distinguish ix i3 i1, ! Distinguish ix i3 i2, ! Distinguish ix i3 i4,
    ! Distinguish ix i4 i1, ! Distinguish ix i4 i2, ! Distinguish ix i4 i3}.

#[program]
Instance Make_StrictProvide4
   `(Provide ix i1, Provide ix i2, Provide ix i3, Provide ix i4,
    ! Distinguish ix i1 i2, ! Distinguish ix i1 i3, ! Distinguish ix i1 i4,
    ! Distinguish ix i2 i1, ! Distinguish ix i2 i3, ! Distinguish ix i2 i4,
    ! Distinguish ix i3 i1, ! Distinguish ix i3 i2, ! Distinguish ix i3 i4,
    ! Distinguish ix i4 i1, ! Distinguish ix i4 i2, ! Distinguish ix i4 i3)
  : StrictProvide4 ix i1 i2 i3 i4.

Class StrictProvide5 (ix i1 i2 i3 i4 i5 : interface)
   `{Provide ix i1, Provide ix i2, Provide ix i3, Provide ix i4, Provide ix i5,
     ! Distinguish ix i1 i2, ! Distinguish ix i1 i3, ! Distinguish ix i1 i4,
     ! Distinguish ix i1 i5, ! Distinguish ix i2 i1, ! Distinguish ix i2 i3,
     ! Distinguish ix i2 i4, ! Distinguish ix i2 i5, ! Distinguish ix i3 i1,
     ! Distinguish ix i3 i2, ! Distinguish ix i3 i4, ! Distinguish ix i3 i5,
     ! Distinguish ix i4 i1, ! Distinguish ix i4 i2, ! Distinguish ix i4 i3,
     ! Distinguish ix i4 i5, ! Distinguish ix i5 i1, ! Distinguish ix i5 i2,
     ! Distinguish ix i5 i3, ! Distinguish ix i5 i4}.

#[program]
Instance Make_StrictProvide5 (ix i1 i2 i3 i4 i5 : interface)
   `(Provide ix i1, Provide ix i2, Provide ix i3, Provide ix i4, Provide ix i5,
     ! Distinguish ix i1 i2, ! Distinguish ix i1 i3, ! Distinguish ix i1 i4,
     ! Distinguish ix i1 i5, ! Distinguish ix i2 i1, ! Distinguish ix i2 i3,
     ! Distinguish ix i2 i4, ! Distinguish ix i2 i5, ! Distinguish ix i3 i1,
     ! Distinguish ix i3 i2, ! Distinguish ix i3 i4, ! Distinguish ix i3 i5,
     ! Distinguish ix i4 i1, ! Distinguish ix i4 i2, ! Distinguish ix i4 i3,
     ! Distinguish ix i4 i5, ! Distinguish ix i5 i1, ! Distinguish ix i5 i2,
     ! Distinguish ix i5 i3, ! Distinguish ix i5 i4)
  : StrictProvide5 ix i1 i2 i3 i4 i5.

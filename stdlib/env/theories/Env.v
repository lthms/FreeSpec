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

Require Import Coq.ZArith.ZArith.
Require Export Coq.Strings.String.

Require Import Prelude.Control.
Require Import Prelude.Control.Classes.
Require Import Prelude.Data.Z.

Require Import FreeSpec.Exec.
Require Import FreeSpec.Program.
Require Import FreeSpec.Compose.
Require Import FreeSpec.Component.

#[local]
Open Scope prelude_scope.
Open Scope free_scope.
Open Scope string_scope.

Module Env.
  Inductive i: Type -> Type :=
  | GetVar: string -> i string
  | SetVar: string -> string -> i unit.

  Definition get
             {ix} `{Use i ix}
    : string -> Program ix string :=
    request <<< GetVar.

  Definition set
             {ix} `{Use i ix}
             (var: string)
    : string -> Program ix unit :=
    request <<< (SetVar var).
End Env.

Module Args.
  Inductive i: Type -> Type :=
  | Count: i Z
  | Get: Z -> i string.

  Definition count
             {ix} `{Use i ix}
    : Program ix Z :=
    request Count.

  Definition get
             {ix} `{Use i ix}
    : Z -> Program ix string :=
    request <<< Get.
End Args.

#[local]
Close Scope nat_scope.
#[local]
Open Scope Z_scope.

#[local]
Definition component
           {ix} `{Use Env.i ix}
  : Component Args.i unit ix :=
  fun (a:  Type)
      (op: Args.i a)
  => match op with
     | Args.Count
       => Z_of_string <$> lift (Env.get "FREESPEC_EXEC_ARGC")
     | Args.Get idx
       => lift (Env.get (append "FREESPEC_EXEC_ARGV_" (string_of_Z idx)))
     end.

Definition withArgs
           {ix} `{Use Env.i ix}
           {a:  Type}
  : Program (Args.i <+> ix) a -> Program ix a :=
  withComponent (pure tt) component (fun _ => pure tt).

Declare ML Module "stdlib_env_plugin".
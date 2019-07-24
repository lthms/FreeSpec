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

From FreeSpec Require Export Core.
From FreeSpec.Exec Require Export Debug.

Declare ML Module "exec_plugin".

#[local]
Fixpoint extends {ix j a s} (init : s) (c : component j ix s) (p : impure (j ⊕ ix) a)
  : impure ix (a * s) :=
  match p with
  | local x => local (x, init)
  | request_then (in_left e) f =>
    var res <- c _ e init in
    extends (snd res) c (f (fst res))
  | request_then (in_right e) f =>
    request_then e (fun x => extends init c (f x))
  end.

(** With FreeSpec.Exec, it becomes possible to interpret a term of type [Program
    Ix A], where [Ix] depends on the plugins loaded by the user.

    In addition, we provide [withComponent], a helper function to extend the set
    of interfaces that can be executed with FreeSpec [Component]s. There are
    several advantages to rely on [withComponent] rather than writing an OCaml
    plugin, the most important being a handler in Coq is not part of the
    TCB. Besides, it can be verified as any FreeSpec [Component]. *)
Definition withComponent {ix j a s}
  (** A [Component] carries its own state. The [initializer] is a
    computation to construct the initial state of the component *)
  (initializer : impure ix s)
  (** The [Component] used to implement a semantics for J *)
  (c : component j ix s)
  (** The [finalizer] is a clean-up computation to “destruct” the [Component]
      final state *)
   (finalizer : s -> impure ix unit)
   (** A computation to interpret, that uses [J] in addition to [Ix]. *)
   (p : impure (j ⊕ ix) a)
  : impure ix a :=
  var s <- initializer in
  var res <- extends s c p in
  do finalizer (snd res);
     pure (fst res).

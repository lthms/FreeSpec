(* FreeSpec
 * Copyright (C) 2018 ANSSI
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

Require Import FreeSpec.Concurrent.
Require Import FreeSpec.Specification.
Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Classes.
Require Import FreeSpec.Control.State.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Program.
Require Import FreeSpec.Refine.
Require Import FreeSpec.WEq.

Set Implicit Arguments.

Section PROXY.
  Variables (I Ii Io:     Interface)
            (S:           Type)
            (proxy:       StatefulRefinement Ii Io S)
            (to_proxy:    forall (A:  Type), I A -> option (Ii A))
            (from_proxy:  forall (A:  Type), Io A -> I A).

  Definition proxy_aux
             {A:    Type}
             (sig:  Semantics I)
             (s:    S)
             (e:    I A)
    : (A * S * Semantics I) :=
    match to_proxy e with
    | None
      => (evalEffect sig e, s, execEffect sig e)
    | Some i
      => runProgram sig (interface_map (proxy i s) from_proxy)
    end.

  CoFixpoint proxify
             (sig:  Semantics I)
             (s:    S)
    : Semantics I :=
    handler (fun (A:  Type)
                 (e:  I A)
             => ( fst (fst (proxy_aux sig s e))
                , proxify (snd (proxy_aux sig s e))
                          (snd (fst (proxy_aux sig s e)))
                )
            ).

  Section ABSTRACTSPEC.
    Variables (W:      Type)
              (Wi Wo:  Type)
              (c:      Specification W I)
              (ci:     Specification Wi Ii)
              (co:     Specification Wo Io)
              (fi:     W -> Wi)
              (fo:     W -> Wo)
              (sync:   sync_pred W W S).

    Definition out_req_sync
      : Prop :=
      forall (A:  Type)
             (e:  Io A)
             (w:  W),
        precondition co e (fo w)
        -> precondition c (from_proxy e) w.

    Definition in_req_sync
      : Prop :=
      forall (A:   Type)
             (e:   I A)
             (e':  Ii A)
             (w:   W),
        to_proxy e = Some e'
        -> precondition c e w
        -> precondition ci e' (fi w).

    Definition out_prom_sync
      : Prop :=
      forall (A:  Type)
             (e:  Io A)
             (x:  A)
             (w:  W),
        precondition co e (fo w)
        -> postcondition c (from_proxy e) x w
        -> postcondition co e x (fo w).

    Definition in_prom_sync
      : Prop :=
      forall (A:   Type)
             (e:   I A)
             (e':  Ii A)
             (x:   A)
             (w:   W),
        to_proxy e = Some e'
        -> precondition c e w
        -> postcondition ci e' x (fi w)
        -> postcondition c e x w.

    Definition in_unproxy_sync
      : Prop :=
      forall (A:   Type)
             (e:   I A)
             (x:   A)
             (w:   W),
        to_proxy e = None
        -> precondition c e w
        -> postcondition c e x w
        -> fi w = fi (abstract_step c e x w).

    Definition out_unproxy_sync
      : Prop :=
      forall (A:   Type)
             (e:   I A)
             (x:   A)
             (w:   W),
        to_proxy e = None
        -> precondition c e w
        -> postcondition c e x w
        -> fo w = fo (abstract_step c e x w).

    (** Our goal is to be able to prove something like that:

        Theorem proxy_compliant
                (w:  W)
                (s:  S)
                (int:  Semantics I)
                (Hint:  int |= c[w])
          : proxify int s |= c[w].

      By doing that, it become possible to easily adapt a component to
      be used as a proxy. Right now, the best way to do that is to
     *)

  End ABSTRACTSPEC.
End PROXY.
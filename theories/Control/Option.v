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

Require Import FreeSpec.Control.
Require Import FreeSpec.WEq.

Instance option_Functor
  : Functor option :=
  { map := option_map
  }.
+ intros a Ha x.
  cbn.
  induction x; constructor.
  reflexivity.
+ intros a b c Hc u v x.
  induction x; constructor.
  reflexivity.
Defined.

Definition option_app
           (a b:  Type)
           (f:  option (a -> b))
           (x:  option a)
  : option b :=
  match f with
  | Some f
    => f <$> x
  | None
    => None
  end.

Instance option_Applicative
  : Applicative option :=
  { apply := option_app
  ; pure  := fun (a:  Type) => @Some a
  }.
+ intros a Heq x.
  induction x; constructor.
  reflexivity.
+ intros a b c Hc u v w; cbn.
  induction w; induction v; induction u; constructor.
  reflexivity.
+ intros a b Hb v x.
  cbn; constructor.
  reflexivity.
+ intros a b Hb u y.
  cbn; destruct u; constructor.
  reflexivity.
+ intros a b Hb g x.
  destruct x; cbn; constructor.
  reflexivity.
Defined.

Definition option_bind
           (a b:  Type)
           (x:    option a)
           (f:    a -> option b)
  : option b :=
  match x with
  | Some x
    => f x
  | None
    => None
  end.

Instance option_Monad
  : Monad option :=
  { bind := option_bind
  }.
+ intros a b Hb x f.
  cbn.
  reflexivity.
+ intros a Ha x.
  cbn.
  induction x; constructor.
  reflexivity.
+ intros a b c Hc f g h.
  induction f; cbn; [| constructor ].
  induction (g a0); cbn; [| constructor ].
  reflexivity.
+ intros a b Hb x f f' Heq.
  destruct x; cbn; [| constructor ].
  apply Heq.
+ intros a b Hb x f; destruct x; cbn; constructor.
  reflexivity.
Defined.

Definition maybe
           {a b:  Type}
           (f:    a -> b)
           (x:    b)
           (o:    option a)
  : b :=
  match o with
  | Some o
    => f o
  | None
    => x
  end.

Definition unwrap
           {a:  Type}
           (x:  a)
           (o:  option a)
  : a :=
  maybe id x o.
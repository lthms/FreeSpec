Specifying and Composing Components
===================================

Specifying Interfaces
^^^^^^^^^^^^^^^^^^^^^

.. coqtop:: none

   Require Import Coq.Unicode.Utf8.
   Require Import FreeSpec.Interface.

*Interfaces* are the key concept FreeSpec uses in order to reason about
components composition. Following a common practice in functional programming
communities, an interface in FreeSpec is modeled as a parameterized type.

.. coqtop:: out

   Print Interface.

Terms of an interface type represents *operations* to be carried
out by a component which exposes this interface, while the type parameter
represents the type of the operation result.

.. example::

   .. coqtop:: none

      Section Ex1.

      Context (K V:  Type)
              (k:    K)
              (v:    V).

   For instance, consider an interface :g:`map_i` with two operations to read a
   value of type :g:`V` associated to a key of type :g:`K`, and to update the
   value associated to a key. In FreeSpec, we can specify this interface using
   the following datatype:

   .. coqtop:: in

      Inductive map_i: Interface :=
      | Read: K → map_i V
      | Write: K → V → map_i unit.

   Terms of type :g:`map_i` do not carry any notion of operation semantics, but
   they represent a convenient way to designate them, as long as the type of
   their results. For instance, given a key :g:`(k: K)`, the operation to read
   the value associated with this key is identified by:

   .. coqtop:: out

      Check (Read k).

   Because :g:`Read k` is of type :g:`map_i V`, it is expected that the result
   of this operation is of type :g:`V`, which is to be expected in this context.
   Similarly, the operation to change the value associated with :g:`k` with a
   new value :g:`(v: V)` is identified by:

   .. coqtop:: out

      Check (Write k v).

   This time, the type of the result of this operation is :g:`unit`. This is the
   classic approach to handle the “no significant result” case.

   .. coqtop:: none

      End Ex1.

Specifying Computations That Leverages Interfaces
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The :g:`Program` Monad has been originally introduced by the _operational
Haskell package, and FreeSpec used the very same implementation in its first
iterations. Since December 2018, FreeSpec uses an alternative implementation
for the :g:`Program` monad, as depicted by Nicolas Koh *et al.* in `“From C to
Interaction
Trees” <https://www.cis.upenn.edu/~bcpierce/papers/deepweb-overview.pdf>`_. That
being stated, FreeSpec users are not expected to use the :g:`Program`
constructors explicitely.

.. _operational: https://hackage.haskell.org/package/operational

.. coqtop:: none

   Require Import FreeSpec.Program.

.. coqtop:: out

   Check Program.


:g:`Program` is a monad, which means you can use the
:g:`Functor`, :g:`Applicative` and :g:`Monad` functions defined
in `coq-prelude`:

.. coqdoc::

   map : ∀ {I: Interface} {A B: Type}, (A → B) → Program I A → Program I B
   Notation: "<$>"

   pure : ∀ {I: Interface} {A: Type}, A → Program I A

   app : ∀ {I: Interface} {A B: Type}, Program I (A → B) → Program I A
   Notation: "<*>"

   bind : ∀ {I: Interface} {A B: Type},
     Program I A → (A → Program I B) → Program I B
   Notation: ">>="

In addition to these general-purpose functions, FreeSpec
provides one dedicated monadic operation called :g:`request`, to
send an operation of :g:`I` to an implementer (modeled with a
semanics) and waits for its result. However, the definition of
:g:`request` requires us to discuss the :g:`Use` typeclass first,
whose signature is the following:

.. coqtop:: out

   About Use.

The fact that :g:`Program` is parameterized by the interface
that can be used during a given computation is interesting from a
specification point of view. It becomes obvious what a given
computation does, in term of side-effects. However, this makes the
use of several interfaces within the same :g:`Program` instance
harder, in particular in terms of code reusability.

It is a common practice, then, to compose interfaces together
(using :g:`Either`-like datatypes) to create new ones. If a monadic
computation is parameterized with a particular interface :g:`I`, it
cannot be composed with another monadic computation parameterized with
another interface :g:`J`, even if :g:`J` allows for calling
operations of :g:`I`.

The :g:`Use` typeclass —and its already provided instances— is
the way FreeSpec solves this challenge. Rather than specifying a
particular. Given two monadic computations :g:`f` and :g:`g`,
such that:

.. coqdoc::

   f : Program map_i nat
   g : ∀ {Ix: Interface} `{Use map_interface Ix}, Program Ix nat

Then, :g:`g` is stricly more generic (and reusable) than
:g:`f`. This is why the :g:`request` monadic operation leverages
the :g:`Use` typeclass.

.. coqtop:: out

   About request.

When defining an interface, it is a good practice to define helper
functions to use the newly introduced operations more easily.

.. example::

   Going back to the :g:`map_i` interface type we have defined previously, such
   helper functions would like like that:

   .. coqdoc::

      Definition read {ix} `{Use map_i ix} (k: K): Program ix V :=
        request (Read k).

      Definition write {ix} `{Use map_i ix} (k: K) (v: V): Program ix unit :=
        request (Write k v)

   This allows for defining seamlessly more complex monadic
   operations which can use the operations of :g:`map_i`. For instance,
   specifying the program with consists in updating the content
   associated with a key :g:`dst` with the content associated with
   another key :g:`src` can be write as follows:

   .. coqdoc::

      Definition copy {ix} `{Use map_i ix} (src dst: K): Program ix unit :=
        read src >>= write dst.

      Definition copy' {ix} `{Use map_i ix} (src dst: K): Program ix V :=
        x <- read src ;
        write dst x  ;;
        pure x.

Components
^^^^^^^^^^

.. coqtop:: none

   Require Import FreeSpec.Component.
   Require Import Prelude.Control.State.

.. coqtop:: out

   Print Component.

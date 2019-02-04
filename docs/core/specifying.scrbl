#lang scribble/manual

@(require "../macros.scrbl")

@title{Specifying and Composing Components}

@section{Specifying Interfaces}

@para{@italic{Interfaces} are the key concept FreeSpec uses in order to reason
about components composition@.__ Following a common practice in functional
programming communities, an interface in FreeSpec is modeled as a parameterized
type@.__}

@codeblock{Interface = Type @-> Type}

@para{Values of an interface type represents @italic{operations} to be carried
out by a component which exposes this interface, while the type parameter
represents the type of the operation result@.__}

@para{For instance, consider an interface @code{map_i} with two
operations to read a value of type @code{V} associated to a key of type
@code{K}, and to update the value associated to a key. In FreeSpec, we can
specify this interface using the following datatype:}

@margin-note{@italic{How} this value is produced is irrelevant here. We do not
attach any semantics to operations, only a result type@.__}

@verbatim{
Inductive map_i: Interface :=
| Read: K @-> map_i V
| Write: K @-> V @-> map_i unit.
}

@para{Thus, @code{Read k} of type @code{map_i V} represents the
operation of reading the value associated with @code{k}@.__ As stated
by its type, this operation is expected to produce a result of type
@code{V}@.__}

@section{Modeling Components}

@para{A component which exposes an interface @code{I} receives
operations of @code{I}, and computes and sends back to the caller
results for them@.__ To do that, it may need to use other components,
by sending them operations of their own and waiting for their results
as well.}

@subsection{@code{Sem.t}}

@para{From the caller point of view, the internals of the component
—including which interfaces it uses— is irrelevant. In order to
abstract away these internals, FreeSpec introduces a parameterized
type @code{Sem.t}, such that @code{(@sigma : Sem.t I)} can be used as
an operationa @italic{semantics} for @code{I}.@.__}

@para{FreeSpec introduces the @code{Sem.t} type to model this@.__}

@margin-note{A component which exposes the interface specified by
@code{map_i} will be modeled in FreeSpec by a value of type @code{Sem.t
map_i}@.__}

@codeblock{Sem.t (I: Interface) : Type}

@para{It is one objective of FreeSpec that the concrete implementation
of @code{Sem.t} is irrelevant for most users, as they are not expected
to define them manually@.__ You will only need to understand how the
are implemented in FreeSpec if you need to prove the equivalence
between two distinct operational semantics@.__}

@para{Besides, and even if you should not use them explicitely, there
are two functions to be aware of: @code{evalOperation} and
@code{execOperation}.}

@codeblock{evalOperation : @forall {I: Interface} {A: Type}, Sem.t I @-> I A -> A}

@para{@code{evalOperation} allows for fulfilling the goal of an
operational semantics: computing a result for a given operation@.__}

@codeblock{execOperation : @forall {I: Interface} {A: Type}, Sem.t I @-> I A -> Sem.t I}

@para{@code{execOperation} takes a semantics of a given interface and
an operation of this interface as its input@.__ It returns the new
operational semantics to be used afterward. Most components carries
out their own state to be able to react differently to the same
operation@.__ However, Gallina is a pure functional programming
language, with no notion of implicit, global state@.__ This means
that, given an operational semantics @code{(@sigma : Sem.t I)},
@code{@sigma} will always compute the same result for the same
operation@.__ This is why we consider stream of semantics in
FreeSpec@.__}

@subsection{The @code{Program} Monad}

@para{The @code{Program} Monad has been originally introduced by the
@hyperlink["https://hackage.haskell.org/package/operational"]{operational}
Haskell package, and FreeSpec used the very same implementation in its
first iterations@.__ Since December 2018, FreeSpec uses an alternative
implementation for the @code{Program} monad, as depicted by Nicolas
Koh @italic{et al.} in
@hyperlink["https://www.cis.upenn.edu/~bcpierce/papers/deepweb-overview.pdf"]{“From
C to Interaction Trees”}@.__ That being stated, FreeSpec users are not
expected to use the @code{Program} constructors explicitely.}

@codeblock{Program (I: Interface) (A: Type): Type}

@para{@code{Program} is a monad, which means you can use the
@code{Functor}, @code{Applicative} and @code{Monad} functions defined
in @tt{coq-prelude}:}

@codeblock{map : @forall {I: Interface} {A B: Type}, (A @-> B) @-> Program I A @-> Program I B
Notation: "<$>"

pure : @forall {I: Interface} {A: Type}, A @-> Program I A

app : @forall {I: Interface} {A B: Type}, Program I (A @-> B) @-> Program I A
Notation: "<*>"

bind : @forall {I: Interface} {A B: Type},
  Program I A @-> (A @-> Program I B) @-> Program I B
Notation: ">>="}

@subsection{@code{request}}

@para{In addition to these general-purpose functions, FreeSpec
provides one dedicated monadic operation called @code{request}, to
send an operation of @code{I} to an implementer (modeled with a
semanics) and waits for its result@.__ However, the definition of
@code{request} requires us to discuss the @code{Use} typeclass first,
whose signature is the following:}

@codeblock{Class Use (I: Interface) (Ix: Interface)}

@para{The fact that @code{Program} is parameterized by the interface
that can be used during a given computation is interesting from a
specification point of view@.__ It becomes obvious what a given
computation does, in term of side-effects@.__ However, this makes the
use of several interfaces within the same @code{Program} instance
harder, in particular in terms of code reusability@.__}

@para{It is a common practice, then, to compose interfaces together
(using @code{Either}-like datatypes) to create new ones. If a monadic
computation is parameterized with a particular interface @code{I}, it
cannot be composed with another monadic computation parameterized with
another interface @code{J}, even if @code{J} allows for calling
operations of @code{I}@.__}

@para{The @code{Use} typeclass —and its already provided instances— is
the way FreeSpec solves this challenge. Rather than specifying a
particular@.__ Given two monadic computations @code{f} and @code{g},
such that:}

@verbatim{
f : Program map_i nat
g : @forall {Ix: Interface} `{Use map_interface Ix}, Program Ix nat
}

@para{Then, @code{g} is stricly more generic (and reusable) than
@code{f}. This is why the @code{request} monadic operation leverages
the @code{Use} typeclass.}

@codeblock{request : @forall {i ix: Interface} `{Use i ix} {A: Type}, i A @-> Program ix A}

@para{When defining an interface, it is a good practice to define helper
functions to use the newly introduced operations more easily@.__}

@verbatim{
Definition read {ix} `{Use map_i ix} (k: K): Program ix V :=
  request (Read k).

Definition write {ix} `{Use map_i ix} (k: K) (v: V): Program ix unit :=
  request (Write k v)
}

@para{This allows for defining seamlessly more complex monadic
operations which can use the operations of @code{map_i}. For instance,
specifying the program with consists in updating the content
associated with a key @code{dst} with the content associated with
another key @code{src} can be write as follows:}

@verbatim{
Definition copy {ix} `{Use map_i ix} (src dst: K): Program ix unit :=
  read src >>= write dst.

Definition copy' {ix} `{Use map_i ix} (src dst: K): Program ix V :=
  x <- read src ;
  write dst x  ;;
  pure x.
}

@subsection{@code{Component}}

@codeblock{
Component (I: Interface) (S: Type) (J: Interface) =
  @forall {A: Type}, I A @-> StateT (Program J) S A
}

@subsection{@code{mkSemantics}}

@codeblock{
mkSemantics : @forall {I J: Interface} {S: Type},
  Component I J S @-> Sem.t J @-> S @-> Sem.t I
}

What if a given component is self-sufficient (meaning it does not use any
particular interface to compute the results of the operations it receives)?

@codeblock{
</> : Interface
}

@codeblock{
none_machine : Sem.t </>
}

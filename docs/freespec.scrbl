#lang scribble/manual

@author{the ANSSI (Cybersecurity Agency of France)}

@title{FreeSpec}

@para{FreeSpec is a @italic{compositional reasoning} framework for the Coq proof
assistant@.__ It allows for building up a complex system by connecting
components together through well defined @italic{interfaces}@.__ It also allows
for reasoning about the correctness about the system, thanks to so-called
@italic{abstract specification}. Components are verified in isolation, following
by their @italic{composition} so that local properties can be extended to the
system as a whole.}

@para{FreeSpec leverages popular abstractions in programming language
communities@.__ Components are primilarly identified by the @italic{interface}
(the set of operations) they expose for other components to use, and secondarily
by the interfaces they use@.__ Then, components are modeled as “program of
effects” of the interfaces they use, and can act as “effects handler” for the
interface they expose@.__}

@para{The present manual presents the key concepts of FreeSpec, and its various
extensions@.__}

@table-of-contents[]

@include-section{core.scrbl}
@include-section{experiment.scrbl}
@include-section{exec.scrbl}

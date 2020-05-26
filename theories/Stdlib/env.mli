open Coqbase

val getenv : Bytestring.t -> Bytestring.t option [@@impure]
val setenv : Bytestring.t -> Bytestring.t -> unit [@@impure]

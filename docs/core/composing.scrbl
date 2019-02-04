#lang scribble/manual

@(require "../macros.scrbl")

@title{Components Composition}

@codeblock{
(<+>) : @forall (I J: Interface), Interface
}

@codeblock{
(<x>) : @forall {I J: Interface}, Sem.t I @-> Sem.t J -> Sem.t (I <+> J)
}

@codeblock{
(<·>) : @forall {I J: Interface} {W_I W_J: Type},
  Specs I W_J @-> Specs J W_J @-> Specs (I <+> J) (W_I * W_J)
}

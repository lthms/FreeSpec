type 'a reference = 'a ref

val make_ref : 'a -> 'a reference [@@impure]
val deref : 'a reference -> 'a [@@impure]
val assign : 'a reference -> 'a -> unit [@@impure]

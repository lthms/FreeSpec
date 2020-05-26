type 'a t

val create : unit -> 'a t
val add : 'a t -> 'a -> Constr.t
val remove : 'a t -> Constr.t -> unit
val find : 'a t -> Constr.t -> 'a
val replace : 'a t -> Constr.t -> 'a -> unit

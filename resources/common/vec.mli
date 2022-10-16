type 'a t

val vec_size : 'a t -> int

val vec_get : 'a t -> int -> 'a

val vec_set : 'a t -> int -> 'a -> unit

val vec_fill : 'a t -> int -> int -> 'a -> unit

val vec_set_size : 'a t -> int -> unit

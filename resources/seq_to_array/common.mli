type 'a t = unit -> 'a node
and 'a node = Nil | Cons of 'a * 'a t
val list_make: int -> 'a -> 'a list
val list_drop: int -> 'a list -> 'a list
val list_take: int -> 'a list -> 'a list
val list_sum: int list -> int
val to_list : 'a t -> 'a list
val fold : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
val length' : 'a t -> int
val iteri : (int -> 'a -> unit) -> 'a t -> unit

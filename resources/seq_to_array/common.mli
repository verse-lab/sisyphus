type 'a t = unit -> 'a node
and 'a node = Nil | Cons of 'a * 'a t
val to_list : 'a t -> 'a list
val fold : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
val length' : 'a t -> int
val iteri : (int -> 'a -> unit) -> 'a t -> unit

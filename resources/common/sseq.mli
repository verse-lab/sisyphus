
type 'a t = unit -> 'a node
and 'a node = Nil | Cons of 'a * 'a t
val fold : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
val length' : 'a t -> int
val iteri : (int -> 'a -> unit) -> 'a t -> unit
val to_list : 'a t -> 'a list
val of_list : 'a list -> 'a t

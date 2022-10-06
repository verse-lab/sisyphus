val array_iter : ('a -> unit) -> 'a array -> unit

val array_take: int -> 'a array -> 'a array

val array_iteri : (int -> 'a -> unit) -> 'a array -> unit

val array_foldi_left : (int -> 'a -> 'b -> 'b) -> 'b -> 'a array -> 'b

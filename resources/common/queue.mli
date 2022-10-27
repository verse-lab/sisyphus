type 'a queue

val queue_unfold: 'a queue -> ('a list * 'a list)

val get_field_left: 'a queue -> 'a list
val set_field_left: 'a queue -> 'a list -> unit

val get_field_right: 'a queue -> 'a list
val set_field_right: 'a queue -> 'a list -> unit

val queue_to_list: 'a queue -> 'a list

val queue_of_list: 'a list -> 'a queue

val queue_init : unit -> 'a queue

val queue_enqueue : 'a queue -> 'a -> unit

val queue_dequeue : 'a queue -> 'a

val queue_iter : ('a -> unit) -> 'a queue -> unit

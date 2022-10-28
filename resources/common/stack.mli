type 'a stack

val stack_of_list: 'a list -> 'a stack

val stack_to_list: 'a stack -> 'a list

val stack_init : unit -> 'a stack

val stack_size : 'a stack -> int

val stack_pop : 'a stack -> 'a

val stack_push : 'a stack -> 'a -> unit

val stack_clear : 'a stack -> unit

val stack_iter : ('a -> unit) -> 'a stack -> unit

val stack_drain : ('a -> unit) -> 'a stack -> unit

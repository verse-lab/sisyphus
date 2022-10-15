type set

val set_mem : int -> set -> bool

val set_add : int -> set -> unit

val set_fold : ('b -> int -> 'b) -> 'b -> set -> 'b

val set_iter : (int -> unit) -> set -> unit

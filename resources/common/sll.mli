
type 'a sll

val sll_cons : 'a -> 'a sll -> 'a sll

val sll_nil : unit -> 'a sll

val sll_push : 'a -> 'a sll -> unit

val sll_iter : ('a -> unit) -> 'a sll -> unit

val sll_iter_drain : ('a -> unit) -> 'a sll -> unit

val sll_fold : ('a -> 'b -> 'b) -> 'b -> 'a sll -> 'b

val sll_reverse : 'a sll -> unit

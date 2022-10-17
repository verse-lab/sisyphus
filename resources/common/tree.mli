type 'a tree

val size : 'a tree -> int

val head : 'a tree -> 'a

val to_list : 'a tree -> 'a list

val of_list : 'a list -> 'a tree

val tree_iter : ('a -> unit) -> 'a tree -> unit

val tree_fold : ('a -> 'b -> 'a) -> 'a -> 'b tree -> 'a

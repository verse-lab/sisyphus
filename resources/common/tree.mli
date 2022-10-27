type 'a tree =
  | Leaf of 'a
  | Node of 'a * 'a tree * 'a tree


val tree_size : 'a tree -> int

val tree_head : 'a tree -> 'a

val tree_to_list : 'a tree -> 'a list

val tree_of_list : 'a list -> 'a tree

val tree_iter : ('a -> unit) -> 'a tree -> unit

val tree_fold : ('a -> 'b -> 'a) -> 'a -> 'b tree -> 'a

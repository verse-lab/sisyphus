val for_upto : int -> int -> (int -> unit) -> unit

val for_downto : int -> int -> (int -> unit) -> unit

val until_downto : int -> int -> (int -> 'a option) -> 'a option

val until_upto : int -> int -> (int -> 'a option) -> 'a option

val while_upto : int -> int -> (int -> bool) -> bool

val while_downto : int -> int -> (int -> bool) -> bool

val nat_fold_up : int -> int -> (int -> 'a -> 'a) -> 'a -> 'a

val nat_fold_down : int -> int -> (int -> 'a -> 'a) -> 'a -> 'a

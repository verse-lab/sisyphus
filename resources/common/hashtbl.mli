type 'a hashtbl

val hashtbl_create : unit -> 'a hashtbl

val hashtbl_remove : 'a hashtbl -> int -> unit

val hashtbl_add : 'a hashtbl -> int -> 'a -> unit

val hashtbl_fold : 'a hashtbl -> ('c -> int * 'a -> 'c) -> 'c -> 'c

val hashtbl_iter : 'a hashtbl -> (int * 'a -> unit) -> unit

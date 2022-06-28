type 'a gen = unit -> 'a option

type 'a node =
  | Nil
  | Cons of 'a array * int ref * 'a node ref
  | Cons1 of 'a * 'a node ref
  | Suspend of 'a gen

type 'a t = {
  start : 'a node ref; (* first node. *)
  mutable chunk_size : int;
  max_chunk_size : int;
}

(* increment the size of chunks *)
let _incr_chunk_size mlist =
  if mlist.chunk_size < mlist.max_chunk_size
  then mlist.chunk_size <- 2 * mlist.chunk_size

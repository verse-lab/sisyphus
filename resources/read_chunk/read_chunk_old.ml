open Common

(* read one chunk of input; return the corresponding node.
   will potentially change [mlist.chunk_size]. *)
let read_chunk mlist gen =
  match gen() with
  | None -> Nil  (* done *)
  | Some x when mlist.max_chunk_size = 1 ->
    let tail = ref (Suspend gen) in
    let node = Cons1 (x, tail) in
    node
  | Some x ->
    (* new list node *)
    let r = ref 1 in
    let a = Array.make mlist.chunk_size x in
    let tail = ref (Suspend gen) in
    let stop = ref false in
    let node = Cons (a, r, tail) in
    (* read the rest of the chunk *)
    while not !stop && !r < mlist.chunk_size do
      match gen() with
      | None ->
        tail := Nil;
        stop := true
      | Some x ->
        a.(!r) <- x;
        incr r;
    done;
    _incr_chunk_size mlist;
    node

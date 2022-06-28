open Common

let read_chunk mlist gen =
  match gen() with
  | None -> Nil  (* done *)
  | Some x when mlist.max_chunk_size = 1 ->
    let tail = ref (Suspend gen) in
    let node = Cons1 (x, tail) in
    node
  | Some x ->
    (* new list node *)
    let a = Array.make mlist.chunk_size x in
    let tail = ref (Suspend gen) in
    let rec aux pos =
      if pos >= mlist.chunk_size
      then pos
      else
      match gen() with
      | None ->
        tail := Nil;
        pos
      | Some x ->
        a.(pos) <- x;
        aux (pos + 1)
    in
    let r = ref (aux 1) in
    let node = Cons (a, r, tail) in
    _incr_chunk_size mlist;
    node

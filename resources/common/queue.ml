type 'a queue = {
  mutable size: int;
  mutable left: 'a list;
  mutable right: 'a list;
}

let queue_init () : 'a queue = { size=0; left = []; right = [] }

let queue_enqueue (q: 'a queue) (hd: 'a) =
  q.size <- q.size + 1;
  q.left <- hd :: q.left

let queue_dequeue (q: 'a queue) =
  assert (q.size > 0);
  q.size <- q.size - 1;
  match q.right with
  | [] ->
    let rev_left = List.rev q.left in
    begin match rev_left with
    | res :: new_right ->
      q.left <- [];
      q.right <- new_right;
      res
    | [] -> assert false
    end
  | res :: new_right ->
    q.right <- new_right;
    res

let queue_iter (f: 'a -> unit) (q: 'a queue) =
  let rev_left = List.rev q.left in
  q.left <- [];
  q.right <- q.right @ rev_left;
  let rec loop ls =
    match ls with
    | [] -> ()
    | h :: t ->
      f h;
      loop t in
  loop q.right
      

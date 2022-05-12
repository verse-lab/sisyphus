open Common

let to_array (s: ('a t[@collection Common.of_list])) =
  (* 0 *)
  let ((len: int), (ls: 'a list))[@rewrite list_fold_length_rev] =
    fold (fun ((i: int), (acc: 'a list)) (x: 'a) -> (i + 1, x :: acc)) (0, []) s in
   (* 1 *)
   match ls with
     | [] -> (* 2 *) [| |]
     | (init: 'a)::(rest: 'a list) ->
       (* 3 *)
       let (a: 'a array) = Array.make len init in
       (* 4 *)
       (* Subtract 1 for len->index conversion and 1 for the removed [init] *)
       let (idx: int) = len - 2 in
       (* 5 *)
       let _ = List.fold_left (fun (i: int) (x: 'a) -> a.(i) <- x; i - 1) idx rest in
       (* 6 *)
       a

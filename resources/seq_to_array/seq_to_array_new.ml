open Sseq

let to_array (s: ('a Sseq.t[@collection Sseq.of_list, Sseq.to_list])) =
  (* 1 *)
  let ((len: int), (ls: 'a list))[@rewrite list_fold_length_rev] =
    fold (fun ((i: int), (acc: 'a list)) (x: 'a) -> (* 0 *)(i + 1, x :: acc)) (0, []) s in
   (* 2 *)
   match ls with
     | [] -> (* 3 *) [| |]
     | (init: 'a)::(rest: 'a list) ->
       (* 4 *)
       let (a: 'a array) = Array.make len init in
       (* 5 *)
       let (idx: int) = len - 2 in
       (* 8 *)
       let (unused: int) = List.fold_left (fun (i: int) (x: 'a) -> (* 6 *) a.(i) <- x; (* 7 *) i - 1) idx rest in
       (* 9 *)
       a

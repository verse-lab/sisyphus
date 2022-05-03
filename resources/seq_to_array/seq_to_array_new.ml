open Common

let to_array (l: ('a t[@collection Common.of_list])) =
   let ((len: int), (ls: 'a list)) = fold (fun ((i: int), (acc: 'a list)) (x: 'a) -> (i + 1, x :: acc)) (0, []) l in
   match ls with
     | [] -> [| |]
     | (init: 'a)::(rest: 'a list) ->
       let (a: 'a array) = Array.make len init in
       (* Subtract 1 for len->index conversion and 1 for the removed [init] *)
       let (idx: int) = len - 2 in
       let _ = List.fold_left (fun (i: int) (x: 'a) -> a.(i) <- x; i - 1) idx rest in
       a

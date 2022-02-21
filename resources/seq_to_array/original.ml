let to_array l =
   let len, ls = fold (fun (i, acc) x -> (i + 1, x :: acc)) (0, []) l in
   match ls with
     | [] -> [| |]
     | init::rest ->
       let a = Array.make len init in
       (* Subtract 1 for len->index conversion and 1 for the removed [init] *)
       let idx = len - 2 in
       let _ = List.fold_left (fun i x -> a.(i) <- x; i - 1) idx rest in
       a

let to_array l =
  let len = ref 0 in
  let ls = fold (fun acc x -> incr len; x :: acc) [] l in
   match ls with
     | [] -> [| |]
     | init::rest ->
       let a = Array.make len init in
       (* Subtract 1 for len->index conversion and 1 for the removed [init] *)
       let idx = len - 2 in
       let _ = List.fold_left (fun i x -> a.(i) <- x; i - 1) idx rest in
       a

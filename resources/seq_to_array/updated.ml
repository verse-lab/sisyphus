let to_array l =
  let len, ls = fold (fun (i, acc) x -> (i + 1, x :: acc)) (0, []) l in
   match ls with
     | [] -> [| |]
     | init::rest ->
       let a = Array.make len init in
       (* intros arr, data, Hdata *)
       let idx = len - 2 in
       let _ = List.fold_left (fun i x -> a.(i) <- x; i - 1) idx rest in
       a

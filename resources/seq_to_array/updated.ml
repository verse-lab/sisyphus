let to_array l =
  match l() with
  | Nil -> [| |]
  | Cons (x, _) ->
    let n = length' l in
    let a = Array.make n x in (* need first elem to create [a] *)
    iteri
      (fun i x -> a.(i) <- x)
      l;
    a

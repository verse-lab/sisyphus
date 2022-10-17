  $ ./run_parser.exe seq_to_array
  OLD:
  let to_array (l: ('a) t) =
    match l () with
    | Nil -> [| |]
    | (Cons) ((x: 'a), (_tl: ('a) t)) ->
      let (n: int) = Sseq.length' l in
      let (a: 'a array) = Array.make n x in
      let tmp = (fun (i: int) (x: 'a) -> Array.set a i x) in
      let (unused: unit) = iteri tmp l in a
  NEW:
  let to_array (s: ('a) t) =
    let tmp =
    (fun
      ((i: int), (acc: 'a list)) (x: 'a)
      ->
      (i + 1, x :: acc))
    in
    let ((len: int), (ls: 'a list)) = fold tmp (0, []) s in
    match ls with
    | [] -> [| |]
    | (init: 'a) :: (rest: 'a list) ->
      let (a: 'a array) = Array.make len init in
      let (idx: int) = len - 2 in
      let tmp0 = (fun (i: int) (x: 'a) -> a.(i) <- x; i - 1) in
      let (unused: int) = List.fold_left tmp0 idx rest in
  a

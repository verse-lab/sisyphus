  $ ./run_parser.exe array_map2
  OLD:
  let array_map2 (f: func('a -> 'b -> 'c)) (xs: 'a array) (ys: 'b array) =
    let (len: int) = Array.length xs in
    if len = 0
    then [| |]
    else
    let (zs: 'c array) =
      Array.make len (f (Array.get xs 0) (Array.get ys 0))
    in
    let tmp =
    (fun
      (i: int)
      ->
      zs.(i) <- f (Array.get xs i) (Array.get ys i);
        ())
    in
    let (unused: unit) = for_upto 0 len tmp in zs
  NEW:
  let array_map2 (f:
  func('a -> 'b -> 'c)) (xs: 'a array) (ys: 'b array) =
    let (len: int) = Array.length xs in
    if len = 0
    then [| |]
    else
    let (zs: 'c array) =
      Array.make len (f (Array.get xs 0) (Array.get ys 0))
    in
    let (xs: 'a list) = Array.to_list xs in
    let (ys: 'b list) = Array.to_list ys in
    let (combined: ('a * 'b) list) = List.combine xs ys in
    let tmp =
    (fun
      (i: int) (pair: ('a * 'b))
      ->
      zs.(i) <- f (fst pair) (snd pair);
        ())
    in
    let (unused: () unit) = List.iteri tmp combined in
  zs

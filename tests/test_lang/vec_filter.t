  $ ./run_parser.exe vec_filter
  OLD:
  let vec_filter (p: func('a -> bool)) (v: ('a) t) =
    let (j: int ref) = ref 0 in
    let (n: int) = vec_size v in
    let tmp =
    (fun
      (i: int)
      ->
      let (elt: 'a) = vec_get v i in
        if p elt
        then let (unused: unit) = Vec.vec_set v (! j) elt in j := ! j + 1; ();
        ())
    in
    let (unused: unit) = for_upto 0 n tmp in
    let (unused: unit) = vec_set_size v (! j) in ()
  NEW:
  let vec_filter (p:
  func('a -> bool)) (v: ('a) t) =
    let (j: int ref) = ref 0 in
    let (n: int) = vec_size v in
    let tmp =
    (fun
      (i: int)
      ->
      let (elt: 'a) = vec_get v i in
        if p elt
        then let (unused: unit) = Vec.vec_set v (! j) elt in j := ! j + 1; ();
        ())
    in
    let (unused: unit) = for_upto 0 n tmp in
    if && (> (! j) 0) (< (! j) n)
    then
    let (elt: 'a) = vec_get v 0 in
    let (unused: unit) = Vec.vec_fill v (! j) (n - (! j)) elt in ();
    let (unused: unit) = vec_set_size v (! j) in
   
  ()

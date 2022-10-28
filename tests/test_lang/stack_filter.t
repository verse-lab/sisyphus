  $ ./run_parser.exe stack_filter
  OLD:
  let stack_filter (f: func('a -> bool)) (s: ('a) stack) =
    let (acc: 'a list ref) = ref [] in
    let tmp = (fun (vl: 'a) -> if f vl then acc := vl :: ! acc; (); ()) in
    let (unused: unit) = stack_iter tmp s in
    let (unused: unit) = stack_clear s in
    let (elts: 'a list) = ! acc in
    let tmp0 =
    (fun
      (vl: 'a)
      ->
      let (unused: unit) = stack_push s vl in
        ())
    in
    let (unused: unit) = List.iter tmp0 elts in ()
  NEW:
  let stack_filter (f:
  func('a -> bool)) (s: ('a) stack) =
    let (keep: ('a) stack) = stack_init () in
    let tmp =
    (fun
      (elt: 'a)
      ->
      if f elt then let (unused: unit) = Stack.stack_push keep elt in (); ())
    in
    let (unused: unit) = stack_drain tmp s in
    let tmp0 =
    (fun
      (elt: 'a)
      ->
      let (unused: unit) = Stack.stack_push s elt in
        ())
    in
    let (unused: unit) = stack_drain tmp0 keep in
  ()

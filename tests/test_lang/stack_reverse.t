  $ ./run_parser.exe stack_reverse
  OLD:
  let stack_reverse (s: ('a) stack) =
    let (buf: 'a list ref) = ref [] in
    let tmp = (fun (elt: 'a) -> buf := elt :: ! buf; ()) in
    let (unused: unit) = stack_drain tmp s in
    let (buf: 'a list) = List.rev (! buf) in
    let tmp0 =
    (fun
      (elt: 'a)
      ->
      let (unused: unit) = stack_push s elt in
        ())
    in
    let (unused: unit) = List.iter tmp0 buf in ()
  NEW:
  let stack_reverse (s:
  ('a) stack) =
    let (buf: ('a) queue) = queue_init () in
    let tmp =
    (fun
      (elt: 'a)
      ->
      let (unused: unit) = Queue.queue_enqueue buf elt in
        ())
    in
    let (unused: unit) = stack_drain tmp s in
    let tmp0 = (fun (elt: 'a) -> Stack.stack_push s elt) in
    let (unused: unit) = Queue.queue_iter tmp0 buf in
  ()

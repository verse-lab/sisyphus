open Stack

let stack_reverse (s: 'a stack) =
  let (buf: 'a list ref) = ref [] in
  stack_drain (fun (elt: 'a) ->
    buf := elt :: !buf;
    ()
  ) s;
  let buf = List.rev !buf in
  let (_: unit) = List.iter (fun (elt: 'a) ->
    let (_: unit) = stack_push s elt in
    ()
  ) buf in
  ()

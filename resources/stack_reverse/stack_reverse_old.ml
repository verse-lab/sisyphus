open Stack

let stack_reverse (s: 'a stack) =
  let (buf: 'a list ref) = ref [] in
  let (_: unit) = stack_drain (fun (elt: 'a) ->
    buf := elt :: !buf;
    ()
  ) s in
  let (buf: 'a list) = List.rev !buf in
  let (_: unit) = List.iter (fun (elt: 'a) ->
    let (_: unit) = stack_push s elt in
    ()
  ) buf in
  ()

open Stack

let stack_reverse (s: 'a stack) =
  let (buf: 'a list ref) = ref [] in
  let (_: unit) = stack_drain (fun (elt: 'a) ->
    buf := elt :: !buf;
    ()
  ) s in
  let (buf_contents: 'a list) = List.rev !buf in
  let (_: unit) = List.iter (fun (elt: 'a) ->
    let (_: unit) = stack_push s elt in
    ()
  ) buf_contents in
  ()
[@@with_logical_mapping ["ls", "s"]]
[@@with_opaque_encoding ["stack", ("Stack.stack_of_list", "Stack.stack_to_list")]]

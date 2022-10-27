open Stack

let stack_filter (f: 'a -> bool) (s: 'a stack) =
  let (keep: 'a stack) = stack_init () in
  let (_: unit) = stack_drain (fun (elt: 'a) ->
    if f elt then
      (let (_: unit) = stack_push keep elt in ());
    ()
  ) s in
  let (_: unit) = stack_drain (fun (elt: 'a) ->
    let (_: unit) = stack_push s elt in
    ()
  ) keep in
  ()
[@@with_opaque_encoding ["stack", ("Stack.stack_of_list", "Stack.stack_to_list")]]

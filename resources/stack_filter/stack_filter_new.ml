open Stack

let stack_filter (f: 'a -> bool) (s: 'a stack) =
  let (keep: 'a stack) = stack_init () in
  let (_: unit) = stack_drain (fun (elt: 'a) ->
    if f elt then
      stack_push keep elt;
    ()
  ) s in
  let (_: unit) = stack_drain (fun elt ->
    stack_push s elt
  ) keep in
  ()

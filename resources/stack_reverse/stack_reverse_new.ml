open Stack
open Queue

let stack_reverse (s: 'a stack) =
  let (buf: 'a queue) = queue_init () in
  let (_: unit) = stack_drain (fun (elt: 'a) ->
    let _ = Queue.queue_enqueue buf elt in
    ()
  ) s in
  let (_: unit) = Queue.queue_iter (fun elt ->
    Stack.stack_push s elt
  ) buf in
  ()

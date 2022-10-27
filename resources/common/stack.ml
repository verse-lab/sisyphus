type 'a stack = {
  mutable size: int;
  mutable elements: 'a list
}

let stack_of_list (elts: 'a list) = { size=List.length elts; elements = elts}
let stack_to_list (stack: 'a stack) = stack.elements

let stack_init () : 'a stack = { size=0; elements=[] }

let stack_size (s: 'a stack) : int = s.size

let stack_pop (s: 'a stack) : 'a =
  assert (s.size > 0);
  s.size <- s.size - 1;
  match s.elements with
  | result :: new_elements ->
    s.elements <- new_elements;
    result
  | [] ->
    assert false

let stack_push (s: 'a stack) (hd: 'a) : unit =
  s.size <- s.size + 1;
  s.elements <- hd :: s.elements

let stack_clear (s: 'a stack) : unit =
  s.size <- 0;
  s.elements <- []

let stack_iter f s =
  let rec loop ls =
    match ls with
    | [] -> ()
    | h :: t ->
      f h;
      loop t in
  loop s.elements

let rec stack_drain f s =
  if stack_size s > 0
  then
    let elt = stack_pop s in
    f elt;
    stack_drain f s
  else ()

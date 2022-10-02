let count a =
  let i = ref 0 in
  Array.iter (function true -> incr i | _ -> ()) a;
  !i

let length arr = Array.length arr

let array_iter f a =
  let len = Array.length a in
  let rec loop i =
    if i < len
    then (f a.(i); loop (i + 1))
    else () in
  loop 0

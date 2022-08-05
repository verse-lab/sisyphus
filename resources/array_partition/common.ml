let count a =
  let i = ref 0 in
  Array.iter (function true -> incr i | _ -> ()) a;
  !i

let length arr = Array.length arr

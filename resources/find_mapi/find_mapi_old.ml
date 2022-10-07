open Combinators

let find_mapi a f =
  let len = Array.length a in
  let res = 
    until_upto 0 len (fun i ->
      f i a.(i)
    ) in
  res

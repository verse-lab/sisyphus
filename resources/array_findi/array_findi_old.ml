open Combinators

let findi (t: 'a array) (f: int -> 'a -> bool) =
  let (len: int) = Array.length t in
  let (res: (int * 'a) option) =
    until_upto 0 len (fun (i: int) ->
      if f i t.(i)
      then (Some (i, t.(i)))
      else None) in
  res

open Combinators

let findi (a: 'a array) (f: int -> 'a -> bool) =
  let (len: int) = Array.length a in
  let (res: (int * 'a) option) =
    until_upto 0 len (fun (i: int) ->
      if f i a.(i)
      then (Some (i, a.(i)))
      else None) in
  res
[@@with_logical_mapping ["l", "a"]]

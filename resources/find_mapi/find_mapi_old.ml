open Combinators

let find_mapi (a: 'a array) (f: int -> 'a -> 'b option) =
  let (len: int) = Array.length a in
  let (res: 'b option) = 
    until_upto 0 len (fun (i: int) ->
      f i a.(i)
    ) in
  res

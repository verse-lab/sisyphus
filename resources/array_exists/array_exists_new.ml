open Combinators

let array_exists (a: 'a array) (f: 'a -> bool) =
  let (len: int) = Array.length a in
  let (result: bool option) = until_upto 0 len (fun (i: int) ->
    if f a.(i)
    then Some true
    else None) in
  let (res: bool) = Opt.option_is_some result in
  res

open Combinators
open Opt

let find_mapi (a: 'a array) (f: int -> 'a -> 'b option) =
  let (len: int) = Array.length a in
  if len = 0
  then None
  else
    let (value_found: 'b option ref) = ref None in
    let (_: bool) = while_upto 0 len (fun (i: int) ->
      let (res: 'b option) = f i a.(i) in
      let (found: bool) = option_is_some res in
      if found then
        value_found := res;
      let (res: bool) = not found in
      res
    ) in
    !value_found

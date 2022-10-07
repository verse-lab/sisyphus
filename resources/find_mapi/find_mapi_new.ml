open Combinators
open Opt

let find_mapi a f =
  let len = Array.length a in
  if len = 0
  then None
  else
    let value_found = ref None in
    let _ = while_upto 0 len (fun i ->
      let res = f i a.(i) in
      let found = option_is_some res in
      if found then
        value_found := res;
      let res = not found in
      res
    ) in
    !value_found

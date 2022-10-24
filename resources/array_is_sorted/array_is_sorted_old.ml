open Combinators


let array_is_sorted (a: int array) =
  let (len: int) = Array.length a in
  if len = 0
  then true
  else
    let (res: unit option) = until_downto (len - 1) 0 (fun (i: int) ->
      let (elt: int) = a.(i) in
      let (prev_elt: int) = a.(i - 1) in
      if prev_elt <= elt
      then None
      else Some ()
    ) in
    let (res: bool) = Opt.option_is_some res in
    not res
[@@with_logical_mapping ["l", "a"]]

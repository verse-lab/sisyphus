open Combinators


let array_is_sorted (t: int array) =
  let (len: int) = Array.length t in
  if len = 0
  then true
  else
    let (res: unit option) = until_downto (len - 1) 0 (fun (i: int) ->
      let (elt: int) = t.(i) in
      let (prev_elt: int) = t.(i - 1) in
      if prev_elt <= elt
      then None
      else Some ()
    ) in
    let (res: bool) = Opt.option_is_some res in
    not res

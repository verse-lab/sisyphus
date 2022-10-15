open Combinators

let array_is_sorted (t: int array) =
  let (len: int) = Array.length t in
  if len = 0
  then true
  else
    let (res: unit option) = until_downto (len - 1) 0 (fun (i: int) ->
      if t.(i -1) > t.(i)
      then Some ()
      else None
    ) in
    let (res: bool) = not (Opt.option_is_some res) in
    res

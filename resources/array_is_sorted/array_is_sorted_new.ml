open Combinators

let array_is_sorted (t: int array) =
  let (len: int) = Array.length t in
  if len = 0
  then true
  else
    let (result: bool ref) = ref true in
    let _ = while_downto (len - 1) 0 (fun (i: int) ->
      let (elt: int) = t.(i) in
      let (prev_elt: int) = t.(i - 1) in
      if prev_elt > elt then
        result := false;
      !result
    ) in
    let (res: bool) = !result in
    res

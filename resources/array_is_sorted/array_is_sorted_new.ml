open Combinators

let array_is_sorted (a: int array) =
  let (len: int) = Array.length a in
  if len = 0
  then true
  else
    let (result: bool ref) = ref true in
    let _ = while_downto (len - 1) 0 (fun (i: int) ->
      let (elt: int) = a.(i) in
      let (prev_elt: int) = a.(i - 1) in
      if prev_elt > elt then
        result := false;
      !result
    ) in
    let (res: bool) = !result in
    res

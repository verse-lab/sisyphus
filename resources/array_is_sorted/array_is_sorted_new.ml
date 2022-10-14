open Combinators

let is_sorted (t: int array) =
  let (len: int) = Array.length t in 
  let (result: bool ref) = ref true in
  let (_: bool) = while_downto (len - 1) 0 (fun (i: int) ->
      let (elt_i: int) = t.(i) in
      let (elt_i_prd: int) = t.(i - 1) in
      result := elt_i_prd <= elt_i;
      !result
  ) in
  let res = !result in
  res

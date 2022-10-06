open Arr

let partition p xs =
  let left, right = ref [], ref [] in
  array_iter (fun vl ->
    if p vl
    then left := p :: !left
    else right := p :: !right
  ) xs;
  let left = Array.of_list !left in
  let right = Array.of_list !right in
  left, right

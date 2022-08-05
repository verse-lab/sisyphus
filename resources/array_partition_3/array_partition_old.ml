open Common

let partition p xs =
  let n = length xs in

  let left, right = ref [], ref [] in
  Array.iter (fun vl ->
    if p vl
    then left := p :: !left
    else right := p :: !right
  ) xs;

  let left = Array.of_list !left in
  let right = Array.of_list !right in

  left, right

open Arr

let partition p xs =
  let left, right = ref [], ref [] in
  array_iter (fun vl ->
    if p vl
    then left := vl :: !left
    else right := vl :: !right
  ) xs;
  let left = List.rev !left in
  let right = List.rev !right in
  let left = Array.of_list left in
  let right = Array.of_list right in
  left, right

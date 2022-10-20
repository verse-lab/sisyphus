open Arr

let partition (p: 'a -> bool) (a: 'a array) =
  let (left_ptr: 'a list ref) = ref [] in
  let (right_ptr: 'a list ref) = ref [] in
  let (_: unit) = array_iter (fun (vl: 'a) ->
    let (r: bool) = p vl in
    if r
    then left_ptr := vl :: !left_ptr
    else right_ptr := vl :: !right_ptr
  ) a in
  let (left_l: 'a list) = List.rev !left_ptr in
  let (right_l: 'a list) = List.rev !right_ptr in
  let (left: 'a array) = Array.of_list left_l in
  let (right: 'a array) = Array.of_list right_l in
  left, right

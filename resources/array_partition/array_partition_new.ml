open Arr

let partition (p: 'a -> bool) (xs: 'a array) =
  let (left: 'a list ref) = ref [] in
  let (right: 'a list ref) = ref [] in
  let (_: unit) = array_iter (fun (vl: 'a) ->
    let (r: bool) = p vl in
    if r
    then left := vl :: !left
    else right := vl :: !right
  ) xs in
  let (left: 'a list) = List.rev !left in
  let (right: 'a list) = List.rev !right in
  let (left: 'a array) = Array.of_list left in
  let (right: 'a array) = Array.of_list right in
  left, right

open Arr

let partition (p: 'a -> bool) (xs: 'a array) =
  let (n: int) = Array.length xs in
  if n = 0
  then
    let (a_t : 'a array) = Array.of_list [] in
    let (a_f : 'a array) = Array.of_list [] in
    (a_t, a_f)
  else
    let (left_arr: 'a array) =
      Array.make n (xs.(0)) in
    let (right_arr: 'a array) =
      Array.make n (xs.(0)) in
    let (li: int ref) = ref 0 in
    let (ri: int ref) = ref 0 in
    let (_ : unit) = array_iter (fun (vl: 'a) ->
      if p vl
      then (let (_ : unit) = left_arr.(!li) <- vl in incr li)
      else (let (_: unit) = right_arr.(!ri) <- vl in incr ri)
    ) xs in
    let (left: 'a array) = array_take !li left_arr in
    let (right: 'a array) = array_take !ri right_arr in
    left, right
[@@with_logical_mapping ["l", "xs"; "pp", "p"]]

open Common

let partition (p: 'a -> bool) (xs: 'a array) =
  let (n: int) = Array.length xs in
  if n = 0
  then
    let (a_t : 'a array) = [| |] in
    let (a_f : 'a array) = [| |] in
    (a_t, a_f)
  else
    let (left: 'a array) =
      Array.make n (xs.(0)) in
    let (right: 'a array) =
      Array.make n (xs.(0)) in
    let (li: int ref) = ref 0 in
    let (ri: int ref) = ref 0 in
    array_iter (fun (vl: 'a) ->
      if p vl
      then (left.(!li) <- vl; incr li)
      else (right.(!ri) <- vl; incr ri)
    ) xs;
    let left: 'a array = array_take !li left in
    let right: 'a array = array_take !ri right in
    left, right

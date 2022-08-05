open Common

let partition p xs =
  let n = length xs in
  if n = 0 then ([| |], [| |])
  else
    let left = Array.make n (xs.(0)) in
    let right = Array.make n (xs.(0)) in
    let li = ref 0 in
    let ri = ref 0 in
  Array.iter (fun vl ->
    if p vl
    then (left.(!li) <- vl; incr li)
    else (right.(!ri) <- vl; incr ri)
  ) xs;

  let left = Array.sub left 0 !li in
  let right = Array.sub right 0 !li in

  left, right

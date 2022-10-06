let array_iter f a =
  let len = Array.length a in
  let rec loop i =
    if i < len
    then (f a.(i); loop (i + 1))
    else () in
  loop 0


let array_take i a =
  let len = Array.length a in
  if len = 0 then [| |]
  else
    let sz = if i < len then i else len in
    let arr =
      Array.make sz a.(0) in
    let pos = ref 0 in
    array_iter (fun vl ->
      let ind = !pos in
      incr pos;
      if ind < sz then
        arr.(ind) <- vl
    ) a;
    arr

let array_iteri f t =
  let len = Array.length t in
  let rec aux i =
    if i < len
    then (f i t.(i); aux (i + 1))
    else () in
  aux 0

let array_foldi_left f init t =
  let len = Array.length t in
  let rec aux i acc =
    if i = len then acc
    else aux (i + 1) (f i t.(i) acc)
  in
  aux 0 init

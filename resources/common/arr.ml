let array_iteri f t =
  let len = Array.length t in
  let rec aux i =
    if i = len then ()
    else begin f i t.(i); aux (i + 1) end
  in
  aux 0

let array_foldi_left f init t =
  let len = Array.length t in
  let rec aux i acc =
    if i = len then acc
    else aux (i + 1) (f i t.(i) acc)
  in
  aux 0 init

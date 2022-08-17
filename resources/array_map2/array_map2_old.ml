open Common

let array_map2 f xs ys =
  let lx = Array.length xs in
  let ly = Array.length ys in
  if lx <> ly then raise (Invalid_argument "Misc.array_map2") ;
  let zs = Array.make  lx (f xs.(0) ys.(0)) in
  let rec loop k =
    if k < lx
    then (zs.(k) <- f xs.(k) ys.(k); loop (k + 1))
    else () in
  loop 0;
  zs

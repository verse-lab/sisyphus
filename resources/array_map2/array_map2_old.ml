open Common

let array_map2 f xs ys =
  let lx = Array.length xs and ly = Array.length ys in
  if lx <> ly then raise (Invalid_argument "Misc.array_map2") ;
  let zs = Array.make  lx (f xs.(0) ys.(0)) in
  for k = 0 to lx-1 do
    zs.(k) <- f xs.(k) ys.(k)
  done ;
  zs

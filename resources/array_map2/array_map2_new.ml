open Common

let array_map2 f xs ys =
  let lx = Array.length xs in
  let ly = Array.length ys in
  if lx <> ly then raise (Invalid_argument "Misc.array_map2");
  let zs = Array.make  lx (f xs.(0) ys.(0)) in
  List.iteri (fun i (x, y) -> zs.(i) <- f x y)
    (List.combine (Array.to_list xs) (Array.to_list ys));
  zs



let array_map2 (f: 'a -> 'b -> 'c) (xs: 'a array) (ys: 'b array) =
  let (len: int) = Array.length xs in
  if len = 0
  then [| |]
  else
    let (zs: 'c array) = Array.make len (f xs.(0) ys.(0)) in
    let (lxs: 'a list) = Array.to_list xs in
    let (lys: 'b list) = Array.to_list ys in
    let (combined: ('a * 'b) list) = List.combine lxs lys in
    let (_: unit) = List.iteri (fun (i: int) (pair : 'a * 'b) ->
      zs.(i) <- f (fst pair) (snd pair);
      ()
    ) combined in
    zs

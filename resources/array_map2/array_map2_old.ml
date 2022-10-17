open Combinators

let array_map2 (f: 'a -> 'b -> 'c) (xs: 'a array) (ys: 'b array) =
  let (len: int) = Array.length xs in
  if len = 0
  then [| |]
  else
    let (zs: 'c array) = 
      Array.make len
        (f xs.(0) ys.(0)) in
    let _ = for_upto 0 len (fun (i: int) -> 
      zs.(i) <- f xs.(i) ys.(i);
      ()
    ) in
    zs

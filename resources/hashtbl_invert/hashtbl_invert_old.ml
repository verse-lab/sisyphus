open Hashtbl

let invert_hashtbl (h: int hashtbl) =
  let (c: int hashtbl) = hashtbl_create () in
  let (_: unit) = hashtbl_iter h (fun ((k,v): int * int) ->
    let (_: unit) = hashtbl_add c v k in
    ()
  ) in
  c

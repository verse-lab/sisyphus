open Hashtbl

let invert_hashtbl (h: int hashtbl) =
  let (c: int hashtbl) = hashtbl_create () in
  let (res: int hashtbl) = hashtbl_fold h (fun c ((k,v): int * int) ->
    let (_: unit) = hashtbl_add c v k in
    c
  ) c in
  res

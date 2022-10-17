open Hashtbl

let invert_hashtbl (h: int hashtbl) =
  let (c: int hashtbl) = hashtbl_create () in
  let (res: int hashtbl) = hashtbl_fold h (fun (c: int hashtbl) (((k: int),(v: int))) ->
    let (_: unit) = hashtbl_add c v k in
    c
  ) c in
  res

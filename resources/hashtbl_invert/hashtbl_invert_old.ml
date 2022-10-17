open Hashtbl

let invert_hashtbl (h: int hashtbl) =
  let (c: int hashtbl) = hashtbl_create () in
  let (_: unit) = hashtbl_iter h (fun (((k: int),(v : int))) ->
    let (_: unit) = Hashtbl.hashtbl_add c v k in
    ()
  ) in
  c

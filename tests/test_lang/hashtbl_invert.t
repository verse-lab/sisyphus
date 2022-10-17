  $ ./run_parser.exe hashtbl_invert
  OLD:
  let invert_hashtbl (h: (int) hashtbl) =
    let (c: (int) hashtbl) = hashtbl_create () in
    let tmp =
    (fun
      ((k: int), (v: int))
      ->
      let (unused: () unit) = Hashtbl.hashtbl_add c v k in
        ())
    in
    let (unused: () unit) = hashtbl_iter h tmp in c
  NEW:
  let invert_hashtbl (h:
  (int) hashtbl) =
    let (c: (int) hashtbl) = hashtbl_create () in
    let tmp =
    (fun
      (c: (int) hashtbl) ((k: int), (v: int))
      ->
      let (unused: () unit) = hashtbl_add c v k in
        c)
    in
    let (res: (int) hashtbl) = hashtbl_fold h tmp c in
  res

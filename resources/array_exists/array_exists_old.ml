open Common

let exists t ~f =
  let rec exists_loop t ~f i =
    if i < 0 then false else f t.(i) || exists_loop t ~f (i - 1)
  in
  exists_loop t ~f (length t - 1)

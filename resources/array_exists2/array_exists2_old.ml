open Common

let array_exists2 t1 t2 ~f =
  let rec exists2_exn_loop t1 t2 ~f i =
    if i < 0 then false else f t1.(i) t2.(i) || exists2_exn_loop t1 t2 ~f (i - 1)
  in
  if (Array.length t1) = (Array.length t2)
  then exists2_exn_loop t1 t2 ~f (Array.length t1 - 1)
  else false

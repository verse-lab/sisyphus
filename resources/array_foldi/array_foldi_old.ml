open Common

let foldi t ~init ~f =
  let rec foldi_loop t i ac ~f =
    if i = length t then ac else foldi_loop t (i + 1) (f i ac t.(i)) ~f
  in
  foldi_loop t 0 init ~f

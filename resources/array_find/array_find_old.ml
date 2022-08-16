open Common

let findi t ~f =
  let rec findi_loop t ~f ~length i =
    if i >= length
    then None
    else if f i t.(i)
    then Some (i, t.(i))
    else findi_loop t ~f ~length (i + 1  )
in
  let length = length t in
  findi_loop t ~f ~length 0

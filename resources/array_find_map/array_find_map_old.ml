open Common

let find_map t ~f =
  let rec find_map_loop t ~f ~length i =
    if i >= length
    then None
    else (
      match f t.(i) with
      | None -> find_map_loop t ~f ~length (i + 1)
      | Some _ as res -> res)
  in
  let length = length t in
  find_map_loop t ~f ~length 0

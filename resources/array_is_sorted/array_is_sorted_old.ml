open Common

let is_sorted t ~compare =
  let rec is_sorted_loop t ~compare i =
    if i < 1
    then true
    else compare t.(i - 1) t.(i) <= 0 && is_sorted_loop t ~compare (i - 1)
  in
  is_sorted_loop t ~compare (length t - 1)

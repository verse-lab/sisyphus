open Common

let array_is_sorted t ~compare =
  let rec is_sorted_loop t ~compare i =
    if i < 1
    then true
    else compare t.(i - 1) t.(i) <= 0 && is_sorted_loop t ~compare (i - 1)
  in
  is_sorted_loop t ~compare (Array.length t - 1)

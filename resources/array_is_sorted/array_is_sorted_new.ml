open Common

let is_sorted t ~compare =
  let i = ref (length t - 1) in
  let result = ref true in
  while !i > 0 && !result do
    let elt_i = Array.get t !i in
    let elt_i_minus_1 = Array.get t (!i - 1) in
    if compare elt_i_minus_1 elt_i > 0 then result := false;
    decr i
  done;
  !result 

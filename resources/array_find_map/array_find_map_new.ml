open Common

let find_mapi t ~f =
  let length = length t in
  if length = 0
  then None
  else (
    let i = ref 0 in
    let value_found = ref None in
    while option_is_none !value_found && !i < length do
      let value = Array.get t !i in
      value_found := f !i value;
      incr i
    done;
    !value_found)

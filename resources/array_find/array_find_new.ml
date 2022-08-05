open Common

let findi_internal t ~f ~if_found ~if_not_found =
  let length = length t in
  if length = 0
  then if_not_found ()
  else (
    let i = ref 0 in
    let found = ref false in
    let value_found = ref (Array.get t 0) in
    while (not !found) && !i < length do
      let value = Array.get t !i in
      if f !i value
      then (
        value_found := value;
        found := true)
      else incr i
    done;
    if !found then if_found ~i:!i ~value:!value_found else if_not_found ())

let findi t ~f =
  findi_internal
    t
    ~f
    ~if_found:(fun ~i ~value -> Some (i, value))
    ~if_not_found:(fun () -> None)

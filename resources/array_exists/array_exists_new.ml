open Common

let exists t ~f =
  let i = ref (length t - 1) in
  let result = ref false in
  while !i >= 0 && not !result do
    if f (Array.get t !i) then result := true else decr i
  done;
  !result

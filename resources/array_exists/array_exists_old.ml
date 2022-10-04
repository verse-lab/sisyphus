open Common

let array_exists t ~f =
  let len = Array.length t in
  let result = ref false in
  let _ = while_upto 0 len (fun i ->
    result := f t.(i);
    not !result
  ) in
  !result

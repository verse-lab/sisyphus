open Combinators

let array_exists (t: 'a array) (f: 'a -> bool) =
  let (len: int) = Array.length t in
  let (result: bool ref) = ref false in
  let (_: bool) = while_upto 0 len (fun i ->
    result := f t.(i);
    not !result
  ) in
  let (res: bool) = !result in
  res

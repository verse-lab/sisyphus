open Combinators

let array_exists (a: 'a array) (f: 'a -> bool) =
  let (len: int) = Array.length a in
  let (result: bool ref) = ref false in
  let (_: bool) = while_upto 0 len (fun (i: int) ->
    result := f a.(i);
    not !result
  ) in
  let (res: bool) = !result in
  res
[@@with_logical_mapping ["l", "a"; "fp", "f"]]

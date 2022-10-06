open Combinators
open Opt

let array_exists a ~f =
  let len = Array.length a in
  let res = until_upto 0 len (fun i ->
    if f a.(i)
    then Some true
    else None) in
  option_is_some res

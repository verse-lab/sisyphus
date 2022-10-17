open Combinators
open Vec

let vec_filter (p: 'a -> bool) (v: 'a t) =
  let (j: int ref) = ref 0 in
  let (n: int) = vec_size v in
  let (_: unit) = for_upto 0 n (fun (i: int) ->
    let (elt: 'a) = vec_get v i in
    if p elt then (
      let (_: unit) = Vec.vec_set v !j elt in
      j := !j + 1;
      ()
    );
    ()
  ) in
  let (_: unit) = vec_set_size v !j in
  ()

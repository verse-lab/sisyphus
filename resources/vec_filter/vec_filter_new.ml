open Combinators
open Vec

let vec_filter (p: 'a -> bool) (v: 'a t) =
  let (j: int ref) = ref 0 in
  let (n: int) = vec_size v in
  let (_: unit) = for_upto 0 n (fun (i: int) ->
    let elt = vec_get v i in
    if p elt then (
      Vec.vec_set v !j elt;
      j := !j + 1;
      ()
    );
  ) in
  if !j > 0 && !j < n then (
    let elt = vec_get v 0 in
    Vec.vec_fill v !j (n - !j) elt;
    ()
  );
  let (_: unit) = vec_set_size v !j in
  ()

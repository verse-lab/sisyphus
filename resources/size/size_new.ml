open Common

(* in effect, computes product of nums upto the (n-1th) element of dims *)
let sizes rank dims =
  let a = Array.make rank 1 in
  let len = Array.length dims in
  let prod = ref 1 in
  for i = 0 to len - 1 do
    a.(i) <- !prod;
    prod := !prod * dims.(i);
  done;
  a

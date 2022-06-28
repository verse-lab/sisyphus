open Common

(* in effect, computes product of nums upto the (n-1th) element of dims *)
let sizes rank dims =
  let a = Array.make rank 1 in
  let _ = Array.fold_left (fun (i,s) x -> a.(i)<- s; (i+1, s * x)) (0,1) dims in
  a

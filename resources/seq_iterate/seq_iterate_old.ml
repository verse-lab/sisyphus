open Common

let seq_iterate a v n () =
  let iter = ref 0
  and vn = Array.create n 0.
  and norme = ref 1. in
  let s = ref 0. in
  let max = ref 0. in
  while !norme > eps && !iter < max_iter do
    incr iter;

    for i = 0 to n - 1 do
      s := 0.;
      for j = 0 to n - 1 do
	      s:= !s +. a.(i * n + j) *. v.(j)
      done;
      vn.(i) <- !s
    done;


    max := 0.;
    Array.iter (fun a -> if (abs_float a) > !max then max := (abs_float a) ) vn;
    Array.iteri (fun i a -> vn.(i) <- a /. !max) vn;


    norme := 0.;
    for i = 0 to n  - 1 do
      let diff = abs_float(vn.(i) -. v.(i)) in
      (if !norme < diff then
	       norme := diff
      );
      v.(i) <- vn.(i)

    done;

  done;
  !max, !iter

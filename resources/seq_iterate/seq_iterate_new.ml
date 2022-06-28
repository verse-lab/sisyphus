open Common

let seq_iterate a v n () =
  let vn = Array.create n 0. in
  let s = ref 0. in
  let max = ref 0. in

  let rec aux norme iter =
    if norme > eps && iter < max_iter then begin
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

      let new_norme = ref 0. in
      for i = 0 to n  - 1 do
        let diff = abs_float(vn.(i) -. v.(i)) in
        (if !new_norme < diff then
	         new_norme := diff
        );
        v.(i) <- vn.(i)

      done;

      aux !new_norme (iter + 1)
    end
    else iter
  in
  let iter = aux 1. 0 in
  !max, iter

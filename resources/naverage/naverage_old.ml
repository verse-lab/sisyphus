open Common

(* compute the average list of a list of list of ints *)
let naverage (l: int list list): float list =
  match l with
  | [] -> assert(false)
  | l1 :: _ ->
    let n = float (List.length l) in
    let array_len = List.length l1 in
    let arr = Array.make array_len 0.0 in
    (* accumulate *)
    List.iter (fun li ->
        List.iteri (fun i x ->
            arr.(i) <- arr.(i) +. (float x)
          ) li
      ) l;
    (* average the accumulated *)
    let res = Array.map (fun x -> x /. n) arr in
    Array.to_list res

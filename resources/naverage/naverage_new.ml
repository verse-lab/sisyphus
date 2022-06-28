open Common

(* compute the average list of a list of list of ints *)
let naverage (l: int list list): float list =
  let rec aux arr ls =
    match ls with
    | [] -> arr
    | li :: ls' ->
      List.iteri (fun i x ->
          arr.(i) <- arr.(i) +. (float x)
        ) li;
      aux arr ls'
  in
  let n = float (List.length l) in
  let array_len = List.length (List.hd l) in
  Array.make array_len 0.0
  |> Fun.flip aux l
  |> Array.map (fun x -> x /. n)
  |> Array.to_list

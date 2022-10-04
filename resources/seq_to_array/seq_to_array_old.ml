open Sseq

let to_array (l: ('a Sseq.t[@collection Sseq.of_list, Sseq.to_list])) =
  (* 0 *)
  match l() with
  | Nil -> (* 1 *)
    [| |]
  | Cons ((x: 'a), (_tl: 'a t)) ->
    (* 2 *)
    let (n : int) = Sseq.length' l in
    (* 3 *)
    let (a : 'a array) = Array.make n x in (* need first elem to create [a] *)
    (* 4 *)
    let _ = iteri
      (fun (i: int) (x: 'a) -> a.(i) <- x)
      l in
    (* 5 *)
    a
[@@with_logical_mapping ["s", "l"]]

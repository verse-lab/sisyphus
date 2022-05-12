open Common

let to_array (l: ('a t[@collection Common.of_list])) =
  (* 0 *)
  match l() with
  | Nil -> (* 1 *)
    [| |]
  | Cons ((x: 'a), (_tl: 'a t)) ->
    (* 2 *)
    let (n : int) = length' l in
    (* 3 *)
    let (a : 'a array) = Array.make n x in (* need first elem to create [a] *)
    (* 4 *)
    let _ = iteri
      (fun (i: int) (x: 'a) -> a.(i) <- x)
      l in
    (* 5 *)
    a

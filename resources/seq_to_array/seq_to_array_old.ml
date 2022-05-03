open Common

let to_array (l: ('a t[@collection Common.of_list])) =
  match l() with
  | Nil -> [| |]
  | Cons ((x: 'a), (_tl: 'a t)) ->
    let (n : int) = length' l in
    let (a : 'a array) = Array.make n x in (* need first elem to create [a] *)
    let _ = iteri
      (fun (i: int) (x: 'a) -> a.(i) <- x)
      l in
    a

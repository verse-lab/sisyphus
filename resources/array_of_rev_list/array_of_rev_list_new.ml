open Common

let array_of_rev_list l =
  match l with
    [] -> [| |]
  | x :: tl ->
    let len = List.length l in
    let a = Array.make len x in
    List.iteri (fun i x ->
        a.(len - 1 - i) <- x
      ) l;
    a

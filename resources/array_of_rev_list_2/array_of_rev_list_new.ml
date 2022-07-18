open Common

let array_of_rev_list l =
  match l with
  | [] -> [| |]
  | x :: l' ->
    let rec aux i ls = match ls with
      | [] ->
        i, Array.make i x
      | x :: l' ->
        let len, a = aux (i + 1) l' in
        a.(len - 1 - i) <- x;
        len, a
    in
    let (len, a) = aux 0 l in
    a

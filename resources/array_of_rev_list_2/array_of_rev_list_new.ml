open Common

let array_of_rev_list l =
  match l with
  | [] -> [| |]
  | hd :: tl ->
    let rec aux i ls = match ls with
      | [] ->
        i, Array.make i hd
      | x :: tl ->
        let len, a = aux (i + 1) tl in
        a.(len - 1 - i) <- x;
        len, a
    in
    let (len, a) = aux 0 l in
    a

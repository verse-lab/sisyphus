open Common

let array_of_rev_list (l: 'a list) =
  match l with
    [] -> [| |]
  | (x: 'a) :: (tl: 'a list) ->
    let (len: int) = List.length l in
    let (a: 'a array) = Array.make len x in
    let _ = List.iteri (fun (i: int) (x: 'a) ->
        a.(len - 1 - i) <- x
      ) l in
    a
